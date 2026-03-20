import Exercises.Given.Direction
import Exercises.Given.WithBounds

inductive Color where | black | red
  deriving Repr, DecidableEq


--
-- Definition of `RBTree` and operations on it.
--

/-
1. Every node is read or black.
2. The root is black.
3. The leaves are black.
4. Every red node has only black children.
5. For every node, all its paths to its black leaves have the same length.
-/
inductive RBTree (α : Type) : Color → ℕ → Type where
  | leaf : RBTree α .black 0
  | red_node : α → RBTree α .black k → RBTree α .black k → RBTree α .red k
  | black_node : α → RBTree α cl k → RBTree α cr k → RBTree α .black (k+1)
  deriving Repr

def RBTree.make_black : RBTree α .red k → RBTree α .black (k+1)
  | .red_node a lst rst => .black_node a lst rst

def RBTree.reverse : RBTree α c k → RBTree α c k
  | .leaf => .leaf
  | .black_node a lst rst => .black_node a rst lst
  | .red_node a lst rst => .red_node a rst lst

def RBTree.value : RBTree α .red k → α
  | .red_node a _ _ => a

def RBTree.left_child : RBTree α .red k → RBTree α .black k
  | .red_node _ lst _ => lst

def RBTree.right_child : RBTree α .red k → RBTree α .black k
  | .red_node _ _ rst => rst

def Direction.order (dir : Direction) : RBTree α c k → RBTree α c k := match dir with
  | .left => id
  | .right => RBTree.reverse

def RBTree.pick_child : Direction → RBTree α .red k → RBTree α .black k
  | .left => left_child
  | .right => right_child


--
-- Definition of `RBRoot` and operations on it
--

-- I have made some simplifications to how we work with red-black trees by focusing
-- more on the rooted case.  Internally, the algorithms work with any RBTree, but
-- end-to-end we are only interested in what happens to rooted trees.
-- This lets us simplify the definitions of `Ancestry` and especially `Ancestry_BST`.
structure RBRoot α : Type where
  height : ℕ
  tree : RBTree α .black height
  deriving Repr

def RBTree.to_root (node : RBTree α c k) : RBRoot α :=
  match c with
  | .red => ⟨_, node.make_black⟩
  | .black => ⟨_, node⟩


--
-- Definitions of `Ancestor` and `Ancestry` and operations on them.
--

-- We have two colours and black heigths here:
-- The first of each is the color and black height of the parent, which must match
-- with what the ancestry expects.
-- The second of each is the color and black height of the node that may be placed
-- in the hole.
-- Note that for black parents we pick the colour of the child already: we may need to
-- unpack this structure and change it down the line.  This is what happens when
-- we insert a red node under a black parent.
inductive Ancestor (α : Type) : Color → ℕ → Color → ℕ → Type where
  | red_parent : Direction → α → RBTree α .black k → Ancestor α .red k .black k
  | black_parent : Direction → α → RBTree α sc k → Ancestor α .black (k+1) c k

-- An `Ancestry α c k` is an `RBRoot α` with an `RBTree α c k` misssing.
-- It is essentially a list of `Ancestor`s, with checks to ensure the types match up
-- all the way along the list.
inductive Ancestry (α : Type) : Color → ℕ → Type where
  | root : Ancestry α .black k
  | parent : Ancestor α pc pk c k → Ancestry α pc pk → Ancestry α c k


def Ancestor.rebuild (node : RBTree α c k) : Ancestor α pc pk c k → RBTree α pc pk
  | .red_parent dir pa sib => .red_node pa node sib |> dir.order
  | .black_parent dir pa sib => .black_node pa node sib |> dir.order

def Ancestor.allow_red : Ancestor α .black pk c k → Ancestor α .black pk .red k
  | .black_parent dir pa sib => .black_parent dir pa sib


def Ancestry.rebuild (node : RBTree α c k) :
    Ancestry α c k → RBRoot α
  | .root => node.to_root
  | .parent anc ancs => anc.rebuild node |> ancs.rebuild

def Ancestry.rebuild_and_fix (node : RBTree α .red k) : Ancestry α .black k → RBRoot α
  | .root => node.to_root
  | .parent (pc := pc) (pk := pk) anc ancs =>
      match pc, anc with
      | .red, .red_parent dir pa sib =>
        match ancs with
        | .parent (.black_parent (sc := uc) gdir ga uncle) ancs' => match uc with
            | .black =>
                let topmost : RBTree α .black (pk+1) :=
                  if dir = gdir
                  then
                    let moved_grandpa := .red_node ga sib uncle |> gdir.order
                    .black_node pa node moved_grandpa |> gdir.order
                  else
                    let moved_parent := .red_node pa sib (node.pick_child gdir) |> gdir.order
                    let moved_grandpa := .red_node ga (node.pick_child dir) uncle |> gdir.order
                    .black_node node.value moved_parent moved_grandpa |> gdir.order
                ancs'.rebuild topmost
            | .red =>
                let parent := .black_node pa node sib |> dir.order
                let grandparent := .red_node ga parent uncle.make_black |> gdir.order
                ancs'.rebuild_and_fix grandparent
      | .black, anc' => anc'.allow_red.rebuild node |> ancs.rebuild

--
-- Definition of insertion
--

-- To insert, we find the point to insert at: this is either an `Ancestry` specifying
-- where the new node should be placed, or an indication that the value is already
-- present in the tree.
inductive InsertionPoint (α : Type) : Type where
  | insert_at : Ancestry α .black 0 → InsertionPoint α
  | already_present : InsertionPoint α


def RBTree.find_insertion_point_rec [Ord α] (ai : α) (ancs : Ancestry α c k) :
    RBTree α c k → InsertionPoint α
  | .leaf => .insert_at ancs
  | .red_node a lst rst => match compare ai a with
      | .lt => lst.find_insertion_point_rec ai (.parent (.red_parent .left a rst) ancs)
      | .eq => .already_present
      | .gt => rst.find_insertion_point_rec ai (.parent (.red_parent .right a lst) ancs)
  | .black_node a lst rst => match compare ai a with
      | .lt => lst.find_insertion_point_rec ai (.parent (.black_parent .left a rst) ancs)
      | .eq => .already_present
      | .gt => rst.find_insertion_point_rec ai (.parent (.black_parent .right a lst) ancs)

def RBRoot.find_root_insertion_point [Ord α] (ai : α) (node : RBRoot α) : InsertionPoint α :=
  node.tree.find_insertion_point_rec ai .root

def RBRoot.insert [Ord α] (ai : α) (node : RBRoot α) : RBRoot α :=
  match node.find_root_insertion_point ai with
  | .insert_at ancs => ancs.rebuild_and_fix (.red_node ai .leaf .leaf)
  | .already_present => node
