package trie

import (
	"bytes"
	"errors"
	"fmt"
	"io"
	"math/big"
	"sync"

	zkt "github.com/scroll-tech/zktrie/types"
)

const (
	// proofFlagsLen is the byte length of the flags in the proof header
	// (first 32 bytes).
	proofFlagsLen = 2
)

var (
	// ErrNodeKeyAlreadyExists is used when a node key already exists.
	ErrInvalidField = errors.New("Key not inside the Finite Field")
	// ErrNodeKeyAlreadyExists is used when a node key already exists.
	ErrNodeKeyAlreadyExists = errors.New("key already exists")
	// ErrKeyNotFound is used when a key is not found in the ZkTrieImpl.
	ErrKeyNotFound = errors.New("key not found in ZkTrieImpl")
	// ErrNodeBytesBadSize is used when the data of a node has an incorrect
	// size and can't be parsed.
	ErrNodeBytesBadSize = errors.New("node data has incorrect size in the DB")
	// ErrReachedMaxLevel is used when a traversal of the MT reaches the
	// maximum level.
	ErrReachedMaxLevel = errors.New("reached maximum level of the merkle tree")
	// ErrInvalidNodeFound is used when an invalid node is found and can't
	// be parsed.
	ErrInvalidNodeFound = errors.New("found an invalid node in the DB")
	// ErrInvalidProofBytes is used when a serialized proof is invalid.
	ErrInvalidProofBytes = errors.New("the serialized proof is invalid")
	// ErrEntryIndexAlreadyExists is used when the entry index already
	// exists in the tree.
	ErrEntryIndexAlreadyExists = errors.New("the entry index already exists in the tree")
	// ErrNotWritable is used when the ZkTrieImpl is not writable and a
	// write function is called
	ErrNotWritable = errors.New("merkle Tree not writable")

	dbKeyRootNode = []byte("currentroot")
)

// ZkTrieImpl is the struct with the main elements of the ZkTrieImpl
type ZkTrieImpl struct {
	db        ZktrieDatabase
	writable  bool
	maxLevels int
	Debug     bool
	root      node
	unhashed  int
}

func NewZkTrieImpl(storage ZktrieDatabase, maxLevels int) (*ZkTrieImpl, error) {
	return NewZkTrieImplWithRoot(storage, &zkt.HashZero, maxLevels)
}

// NewZkTrieImplWithRoot loads a new ZkTrieImpl. If in the storage already exists one
// will open that one, if not, will create a new one.
func NewZkTrieImplWithRoot(storage ZktrieDatabase, rootHash *zkt.Hash, maxLevels int) (*ZkTrieImpl, error) {
	mt := ZkTrieImpl{db: storage, maxLevels: maxLevels, writable: true, root: hashNode{rootHash}}
	if *rootHash != zkt.HashZero {
		_, err := mt.GetNode(rootHash)
		if err != nil {
			return nil, err
		}
	} else {
		mt.root = &Empty
	}
	return &mt, nil
}

// Commit write all nodes to database
func (mt *ZkTrieImpl) Commit() error {
	var err error
	mt.Root()

	if !mt.writable {
		return ErrNotWritable
	}
	mt.root, err = mt.commit(mt.root)
	if err != nil {
		return err
	}
	err = mt.dbInsert(dbKeyRootNode, DBEntryTypeRoot, mt.Root()[:])
	return err
}

func (mt *ZkTrieImpl) commit(n node) (node, error) {
	var err error
	switch n := n.(type) {
	case *midNode:
		if n.flags.dirty {
			n.childL, err = mt.commit(n.childL)
			if err != nil {
				return n.childL, err
			}
			n.childR, err = mt.commit(n.childR)
			if err != nil {
				return n.childR, err
			}

			enc := n.CanonicalValue()
			err = mt.dbPut(n.flags.cached.Hash[:], enc)
			n.flags.dirty = false
			cached := n.flags.cached
			recyclingMidNode(n)
			return cached, err
		}
		return n, nil
	case *leafNode:
		enc := n.CanonicalValue()
		k, err := n.Key()
		if err != nil {
			return nil, err
		}
		err = mt.dbPut(k[:], enc)
		return hashNode{k}, err
	case *emptyNode:
		return &Empty, nil
	case hashNode:
		return n, nil
	default:
		return nil, ErrInvalidNodeFound
	}
}

func (mt *ZkTrieImpl) Root() *zkt.Hash {
	var root *zkt.Hash
	if mt.unhashed >= 100 {
		root = mt.hashRoot(mt.root, 16)
	} else {
		root = mt.hashRoot(mt.root, 0)
	}
	mt.unhashed = 0
	return root
}

func (mt *ZkTrieImpl) hashRoot(n node, parallel int) *zkt.Hash {
	switch n := n.(type) {
	case *midNode:
		if n.flags.cached.Hash == nil {
			var left, right *zkt.Hash
			if parallel >= 2 {
				var wg sync.WaitGroup
				wg.Add(2)
				go func() {
					left = mt.hashRoot(n.childL, parallel/2)
					wg.Done()
				}()
				go func() {
					right = mt.hashRoot(n.childR, parallel-parallel/2)
					wg.Done()
				}()
				wg.Wait()
			} else {
				left = mt.hashRoot(n.childL, 0)
				right = mt.hashRoot(n.childR, 0)
			}

			r, err := zkt.HashElems(left.BigInt(), right.BigInt())
			// fmt.Println(left.Hex()[:8], ",", right.Hex()[:8], "=>", r.Hex()[:8])
			if err != nil {
				panic("zkt.HashElems fail")
			}
			n.flags.cached = hashNode{r}
		}
		return n.flags.cached.Hash
	case hashNode:
		return n.Hash
	case *leafNode:
		h, err := n.Key()
		if err != nil {
			panic("leafNode Key() error")
		}
		return h
	case *emptyNode:
		return &zkt.HashZero
	default:
		panic("ErrInvalidNodeFound")
	}
}

// MaxLevels returns the MT maximum level
func (mt *ZkTrieImpl) MaxLevels() int {
	return mt.maxLevels
}

// tryUpdate update a Key & Value into the ZkTrieImpl. Where the `k` determines the
// path from the Root to the Leaf. This also return the updated leaf node
func (mt *ZkTrieImpl) TryUpdate(kHash *zkt.Hash, vFlag uint32, vPreimage []zkt.Byte32) error {

	// verify that the ZkTrieImpl is writable
	if !mt.writable {
		return ErrNotWritable
	}

	// verify that k are valid and fit inside the Finite Field.
	if !zkt.CheckBigIntInField(kHash.BigInt()) {
		return ErrInvalidField
	}

	//newNodeLeaf := NewNodeLeaf(kHash, vFlag, vPreimage)
	newNodeLeaf := leafNode{NodeKey: kHash, CompressedFlags: vFlag, ValuePreimage: vPreimage}
	path := getPath(mt.maxLevels, kHash[:])

	// precalc Key of new leaf here
	if _, err := newNodeLeaf.Key(); err != nil {
		return err
	}
	ok, newRoot, err := mt.insert(mt.root, &newNodeLeaf, kHash, 0, path, true)
	if ok {
		mt.unhashed++
	}
	// sanity check
	if err == ErrEntryIndexAlreadyExists {
		panic("Encounter unexpected errortype: ErrEntryIndexAlreadyExists")
	} else if err != nil {
		return err
	}
	mt.root = newRoot
	return nil
}

func (mt *ZkTrieImpl) delRecursive(n node, kHash *zkt.Hash, path []bool, lvl int) (bool, node, error) {
	var err error
	if hnode, ok := n.(hashNode); ok {
		n, err = mt.resolveHash(hnode, nil)
		if err != nil {
			return false, n, err
		}
	}

	switch n := n.(type) {
	case *leafNode:
		if bytes.Equal(n.NodeKey[:], kHash[:]) {
			return true, &Empty, nil
		} else { //not found
			return false, n, ErrKeyNotFound
		}
	case *midNode:
		var dirty bool
		if path[lvl] {
			dirty, n.childR, err = mt.delRecursive(n.childR, kHash, path, lvl+1)
			if err != nil {
				return false, n, err
			}
			if hnode, ok := n.childL.(hashNode); ok {
				n.childL, err = mt.resolveHash(hnode, nil)
				if err != nil {
					return false, n, err
				}
			}
		} else {
			dirty, n.childL, err = mt.delRecursive(n.childL, kHash, path, lvl+1)
			if err != nil {
				return false, n, err
			}
			if hnode, ok := n.childR.(hashNode); ok {
				n.childR, err = mt.resolveHash(hnode, nil)
				if err != nil {
					return false, n, err
				}
			}
		}
		if dirty {
			n.flags = mt.newFlag()
			//if childL is leaf and childR is nil,should "collapse"
			if _, isEmpty := n.childR.(*emptyNode); isEmpty {
				if _, ok := n.childL.(*leafNode); ok {
					return true, n.childL, nil
				}
			}
			//if childR is leaf and childL is nil,should "collapse"
			if _, isEmpty := n.childL.(*emptyNode); isEmpty {
				if _, isLeaf := n.childR.(*leafNode); isLeaf {
					return true, n.childR, nil
				}
			}
		}
		return dirty, n, nil
	case *emptyNode:
		return false, &Empty, ErrKeyNotFound
	default:
		//return false, n, ErrInvalidNodeFound
		panic("ErrInvalidNodeFound")
	}
}
func (mt *ZkTrieImpl) TryDelete(kHash *zkt.Hash) error {
	return mt.tryDeleteLite(kHash)
}

func (mt *ZkTrieImpl) tryDeleteLite(kHash *zkt.Hash) error {
	// verify that the ZkTrieImpl is writable
	if !mt.writable {
		return ErrNotWritable
	}

	// verify that k is valid and fit inside the Finite Field.
	if !zkt.CheckBigIntInField(kHash.BigInt()) {
		return ErrInvalidField
	}
	path := getPath(mt.maxLevels, kHash[:])

	ok, newRoot, err := mt.delRecursive(mt.root, kHash, path, 0)
	if err != nil {
		return err
	}
	mt.root = newRoot
	if ok {
		mt.unhashed++
	}
	return nil
}

func (t *ZkTrieImpl) newFlag() nodeFlag {
	return nodeFlag{dirty: true}
}

func (mt *ZkTrieImpl) insert(n node, newLeaf *leafNode, key *zkt.Hash,
	lvl int, path []bool, forceUpdate bool) (bool, node, error) {
	if lvl > mt.maxLevels-1 {
		return false, nil, ErrReachedMaxLevel
	}
	switch n := n.(type) {
	case *emptyNode:
		return true, newLeaf, nil
	case *midNode:
		var dirty bool
		var err error

		if path[lvl] {
			dirty, n.childR, err = mt.insert(n.childR, newLeaf, key, lvl+1, path, forceUpdate)
			if err != nil {
				return false, nil, err
			}
		} else {
			dirty, n.childL, err = mt.insert(n.childL, newLeaf, key, lvl+1, path, forceUpdate)
			if err != nil {
				return false, nil, err
			}
		}
		n.flags = mt.newFlag()
		return dirty, n, nil
	case hashNode:
		nodeExpanded, err := mt.resolveHash(n, nil)
		if err != nil {
			return false, nil, err
		}
		return mt.insert(nodeExpanded, newLeaf, key, lvl, path, forceUpdate)
	case *leafNode:
		// exists key,replace or ignore
		if bytes.Equal(newLeaf.NodeKey[:], n.NodeKey[:]) {
			kOld, err := n.Key()
			if err != nil {
				return false, nil, err
			}
			kNew, err := newLeaf.Key()
			if err != nil {
				return false, nil, err
			}

			if bytes.Equal(kOld[:], kNew[:]) {
				return false, n, nil
			} else {
				if forceUpdate {
					return true, newLeaf, nil
				} else {
					return false, nil, ErrEntryIndexAlreadyExists
				}
			}
		}
		//
		pathOldLeaf := getPath(mt.maxLevels, n.NodeKey[:])
		top := midNodePool.Get().(*midNode)

		pre := top
		i := lvl
		for ; i < mt.maxLevels && path[i] == pathOldLeaf[i]; i++ {
			nm := midNodePool.Get().(*midNode)
			if path[i] {
				pre.childR = nm
			} else {
				pre.childL = nm
			}
			pre = nm
		}
		if i == mt.maxLevels {
			return false, nil, ErrReachedMaxLevel
		}
		if path[i] {
			pre.childR = newLeaf
			pre.childL = n
		} else {
			pre.childR = n
			pre.childL = newLeaf
		}
		return true, top, nil

	default:
		return false, nil, ErrInvalidNodeFound
	}
}

func (mt *ZkTrieImpl) resolveHash(n hashNode, prefix []byte) (node, error) {
	if bytes.Equal(n.Hash[:], zkt.HashZero[:]) {
		return &Empty, nil
	}
	enc, err := mt.db.Get(n.Hash[:])
	if err != nil {
		return nil, err
	}
	return nodeFromBytes(n, enc)
}

func (mt *ZkTrieImpl) tryGet(kHash *zkt.Hash) (*Node, []*zkt.Hash, error) {
	path := getPath(mt.maxLevels, kHash[:])
	nextKey := mt.Root()
	var siblings []*zkt.Hash
	for i := 0; i < mt.maxLevels; i++ {
		n, err := mt.GetNode(nextKey)
		if err != nil {
			return nil, nil, err
		}
		switch n.Type {
		case NodeTypeEmpty:
			return NewNodeEmpty(), siblings, ErrKeyNotFound
		case NodeTypeLeaf:
			if bytes.Equal(kHash[:], n.NodeKey[:]) {
				return n, siblings, nil
			}
			return n, siblings, ErrKeyNotFound
		case NodeTypeMiddle:
			if path[i] {
				nextKey = n.ChildR
				siblings = append(siblings, n.ChildL)
			} else {
				nextKey = n.ChildL
				siblings = append(siblings, n.ChildR)
			}
		default:
			return nil, nil, ErrInvalidNodeFound
		}
	}
	return nil, siblings, ErrReachedMaxLevel
}

// TryGet returns the value for key stored in the trie.
// The value bytes must not be modified by the caller.
// If a node was not found in the database, a MissingNodeError is returned.
func (mt *ZkTrieImpl) TryGet(kHash *zkt.Hash) ([]byte, error) {
	var err error
	path := getPath(mt.maxLevels, kHash[:])
	n := mt.root
	for i := 0; i < mt.maxLevels; {
		switch nd := n.(type) {
		case *leafNode:
			if bytes.Equal((*nd.NodeKey)[:], (*kHash)[:]) {
				return nd.Data(), nil
			}
			return nil, ErrKeyNotFound
		case *midNode:
			if path[i] {
				n = nd.childR
			} else {
				n = nd.childL
			}
			i++
		case hashNode:
			n, err = mt.resolveHash(nd, nil)
			if err != nil {
				return nil, err
			}
		case *emptyNode:
			return nil, ErrKeyNotFound
		default:
			return nil, ErrInvalidNodeFound
		}
	}
	return nil, ErrKeyNotFound
}

// dbInsert is a helper function to insert a node into a key in an open db
// transaction.
func (mt *ZkTrieImpl) dbInsert(k []byte, t NodeType, data []byte) error {
	v := append([]byte{byte(t)}, data...)
	return mt.dbPut(k, v)
}

func (mt *ZkTrieImpl) dbPut(k []byte, v []byte) error {
	//fmt.Println("Put:", common.Bytes2Hex(k), ":", common.Bytes2Hex(v))
	return mt.db.Put(k, v)
}

// GetLeafNode is more underlying method than TryGet, which obtain an leaf node
// or nil if not exist
func (mt *ZkTrieImpl) GetLeafNode(kHash *zkt.Hash) (*Node, error) {
	var err error
	path := getPath(mt.maxLevels, kHash[:])
	n := mt.root
	for i := 0; i < mt.maxLevels; i++ {
		if hn, ok := n.(hashNode); ok {
			n, err = mt.resolveHash(hn, nil)
			if err != nil {
				return nil, err
			}
		}
		switch pn := n.(type) {
		case *leafNode:
			if bytes.Equal(kHash[:], pn.NodeKey[:]) {
				return NewNodeLeaf(kHash, pn.CompressedFlags, pn.ValuePreimage), nil
			} else {
				return nil, ErrKeyNotFound
			}
		case *midNode:
			if path[i] {
				n = pn.childR
			} else {
				n = pn.childL
			}
		case nil:
			return nil, ErrKeyNotFound
		default:
			return nil, ErrInvalidNodeFound
		}
	}
	return nil, ErrReachedMaxLevel
}

// GetNode gets a node by key from the MT.  Empty nodes are not stored in the
// tree; they are all the same and assumed to always exist.
// <del>for non exist key, return (NewNodeEmpty(), nil)</del>
func (mt *ZkTrieImpl) GetNode(key *zkt.Hash) (*Node, error) {
	if bytes.Equal(key[:], zkt.HashZero[:]) {
		return NewNodeEmpty(), nil
	}
	nBytes, err := mt.db.Get(key[:])
	if err == ErrKeyNotFound {
		//return NewNodeEmpty(), nil
		return nil, ErrKeyNotFound
	} else if err != nil {
		return nil, err
	}
	return NewNodeFromBytes(nBytes)
}

// getPath returns the binary path, from the root to the leaf.
func getPath(numLevels int, k []byte) []bool {
	path := make([]bool, numLevels)
	for n := 0; n < numLevels; n++ {
		path[n] = zkt.TestBit(k[:], uint(n))
	}
	return path
}

// NodeAux contains the auxiliary node used in a non-existence proof.
type NodeAux struct {
	Key   *zkt.Hash
	Value *zkt.Hash
}

// Proof defines the required elements for a MT proof of existence or
// non-existence.
type Proof struct {
	// existence indicates wether this is a proof of existence or
	// non-existence.
	Existence bool
	// depth indicates how deep in the tree the proof goes.
	depth uint
	// notempties is a bitmap of non-empty Siblings found in Siblings.
	notempties [zkt.ElemBytesLen - proofFlagsLen]byte
	// Siblings is a list of non-empty sibling keys.
	Siblings []*zkt.Hash
	// Key is the key of leaf in existence case
	Key     *zkt.Hash
	NodeAux *NodeAux
}

// BuildZkTrieProof prove uniformed way to turn some data collections into Proof struct
func BuildZkTrieProof(rootKey *zkt.Hash, k *big.Int, lvl int, getNode func(key *zkt.Hash) (*Node, error)) (*Proof,
	*Node, error) {

	p := &Proof{}
	var siblingKey *zkt.Hash

	kHash := zkt.NewHashFromBigInt(k)
	path := getPath(lvl, kHash[:])

	nextKey := rootKey
	for p.depth = 0; p.depth < uint(lvl); p.depth++ {
		n, err := getNode(nextKey)
		if err != nil {
			return nil, nil, err
		}
		switch n.Type {
		case NodeTypeEmpty:
			return p, n, nil
		case NodeTypeLeaf:
			if bytes.Equal(kHash[:], n.NodeKey[:]) {
				p.Existence = true
				return p, n, nil
			}
			// We found a leaf whose entry didn't match hIndex
			p.NodeAux = &NodeAux{Key: n.NodeKey, Value: n.valueHash}
			return p, n, nil
		case NodeTypeMiddle:
			if path[p.depth] {
				nextKey = n.ChildR
				siblingKey = n.ChildL
			} else {
				nextKey = n.ChildL
				siblingKey = n.ChildR
			}
		default:
			return nil, nil, ErrInvalidNodeFound
		}
		if !bytes.Equal(siblingKey[:], zkt.HashZero[:]) {
			zkt.SetBitBigEndian(p.notempties[:], p.depth)
			p.Siblings = append(p.Siblings, siblingKey)
		}
	}
	return nil, nil, ErrKeyNotFound

}

// VerifyProof verifies the Merkle Proof for the entry and root.
func VerifyProofZkTrie(rootKey *zkt.Hash, proof *Proof, node *Node) bool {
	key, err := node.Key()
	if err != nil {
		return false
	}

	rootFromProof, err := proof.Verify(key, node.NodeKey)
	if err != nil {
		return false
	}
	return bytes.Equal(rootKey[:], rootFromProof[:])
}

// Verify the proof and calculate the root, key can be nil when try to verify
// an nonexistent proof
func (proof *Proof) Verify(key, kHash *zkt.Hash) (*zkt.Hash, error) {
	if proof.Existence {
		if key == nil {
			return nil, ErrKeyNotFound
		}
		return proof.rootFromProof(key, kHash)
	} else {

		if proof.NodeAux == nil {
			return proof.rootFromProof(&zkt.HashZero, kHash)
		} else {
			if bytes.Equal(kHash[:], proof.NodeAux.Key[:]) {
				return nil, fmt.Errorf("non-existence proof being checked against hIndex equal to nodeAux")
			}
			midKey, err := LeafKey(proof.NodeAux.Key, proof.NodeAux.Value)
			if err != nil {
				return nil, err
			}
			return proof.rootFromProof(midKey, kHash)
		}
	}

}

func (proof *Proof) rootFromProof(key, kHash *zkt.Hash) (*zkt.Hash, error) {
	midKey := key
	var err error

	sibIdx := len(proof.Siblings) - 1
	path := getPath(int(proof.depth), kHash[:])
	var siblingKey *zkt.Hash
	for lvl := int(proof.depth) - 1; lvl >= 0; lvl-- {
		if zkt.TestBitBigEndian(proof.notempties[:], uint(lvl)) {
			siblingKey = proof.Siblings[sibIdx]
			sibIdx--
		} else {
			siblingKey = &zkt.HashZero
		}
		if path[lvl] {
			midKey, err = NewNodeMiddle(siblingKey, midKey).Key()
			if err != nil {
				return nil, err
			}
		} else {
			midKey, err = NewNodeMiddle(midKey, siblingKey).Key()
			if err != nil {
				return nil, err
			}
		}
	}
	return midKey, nil
}

// walk is a helper recursive function to iterate over all tree branches
func (mt *ZkTrieImpl) walk(key *zkt.Hash, f func(*Node)) error {
	n, err := mt.GetNode(key)
	if err != nil {
		return err
	}
	switch n.Type {
	case NodeTypeEmpty:
		f(n)
	case NodeTypeLeaf:
		f(n)
	case NodeTypeMiddle:
		f(n)
		if err := mt.walk(n.ChildL, f); err != nil {
			return err
		}
		if err := mt.walk(n.ChildR, f); err != nil {
			return err
		}
	default:
		return ErrInvalidNodeFound
	}
	return nil
}

// Walk iterates over all the branches of a ZkTrieImpl with the given rootKey
// if rootKey is nil, it will get the current RootKey of the current state of
// the ZkTrieImpl.  For each node, it calls the f function given in the
// parameters.  See some examples of the Walk function usage in the
// ZkTrieImpl.go and merkletree_test.go
func (mt *ZkTrieImpl) Walk(rootKey *zkt.Hash, f func(*Node)) error {
	if rootKey == nil {
		rootKey = mt.Root()
	}
	err := mt.walk(rootKey, f)
	return err
}

// GraphViz uses Walk function to generate a string GraphViz representation of
// the tree and writes it to w
func (mt *ZkTrieImpl) GraphViz(w io.Writer, rootKey *zkt.Hash) error {
	fmt.Fprintf(w, `digraph hierarchy {
node [fontname=Monospace,fontsize=10,shape=box]
`)
	cnt := 0
	var errIn error
	err := mt.Walk(rootKey, func(n *Node) {
		k, err := n.Key()
		if err != nil {
			errIn = err
		}
		switch n.Type {
		case NodeTypeEmpty:
		case NodeTypeLeaf:
			fmt.Fprintf(w, "\"%v\" [style=filled];\n", k.String())
		case NodeTypeMiddle:
			lr := [2]string{n.ChildL.String(), n.ChildR.String()}
			emptyNodes := ""
			for i := range lr {
				if lr[i] == "0" {
					lr[i] = fmt.Sprintf("empty%v", cnt)
					emptyNodes += fmt.Sprintf("\"%v\" [style=dashed,label=0];\n", lr[i])
					cnt++
				}
			}
			fmt.Fprintf(w, "\"%v\" -> {\"%v\" \"%v\"}\n", k.String(), lr[0], lr[1])
			fmt.Fprint(w, emptyNodes)
		default:
		}
	})
	fmt.Fprintf(w, "}\n")
	if errIn != nil {
		return errIn
	}
	return err
}

// PrintGraphViz prints directly the GraphViz() output
func (mt *ZkTrieImpl) PrintGraphViz(rootKey *zkt.Hash) error {
	if rootKey == nil {
		rootKey = mt.Root()
	}
	w := bytes.NewBufferString("")
	fmt.Fprintf(w,
		"--------\nGraphViz of the ZkTrieImpl with RootKey "+rootKey.BigInt().String()+"\n")
	err := mt.GraphViz(w, nil)
	if err != nil {
		return err
	}
	fmt.Fprintf(w,
		"End of GraphViz of the ZkTrieImpl with RootKey "+rootKey.BigInt().String()+"\n--------\n")

	fmt.Println(w)
	return nil
}
