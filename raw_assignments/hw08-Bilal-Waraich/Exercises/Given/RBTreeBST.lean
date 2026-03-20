import Exercises.Given.Direction
import Exercises.Given.RBTreeDefs
import Exercises.Given.WithBounds

variable {α : Type} [LinearOrder α]

inductive RBTree_BST : (low upp : WithBounds α) → RBTree α c k → Prop where
  | leaf {low upp} : low ≤ upp → RBTree_BST low upp .leaf
  | red_node {low upp a lst rst}
      : RBTree_BST low (.el a) lst
      → RBTree_BST (.el a) upp rst
      → between low a upp
      → RBTree_BST low upp (.red_node a lst rst)
  | black_node {low upp a lst rst}
      : RBTree_BST low (.el a) lst
      → RBTree_BST (.el a) upp rst
      → between low a upp
      → RBTree_BST low upp (.black_node a lst rst)

def RBRoot_BST : RBRoot α → Prop
  | ⟨ _, node ⟩ => RBTree_BST .min .max node

-- I do believe we could reduce the number of cases here with some clever helper functions.
-- However, I also think that this would make the proofs more complicated, since you have
-- to unfold those helper functions and they are likely to get in the way.
-- If you prefer to use a different presentation, you can always define your own
-- predicate and show that it is equivalent, then do your proofs about it instead.
inductive Ancestor_BST : (plow pupp low upp : WithBounds α) → Ancestor α pc pk c k → Prop
  | red_parent_left {plow pupp a sib}
      : RBTree_BST (.el a) pupp sib
      → between plow a pupp
      → Ancestor_BST plow pupp plow (.el a) (.red_parent .left a sib)
  | red_parent_right {plow pupp a sib}
      : RBTree_BST plow (.el a) sib
      → between plow a pupp
      → Ancestor_BST plow pupp (.el a) pupp (.red_parent .right a sib)
  | black_parent_left {plow pupp a sib}
      : RBTree_BST (.el a) pupp sib
      → between plow a pupp
      → Ancestor_BST plow pupp plow (.el a) (.black_parent .left a sib)
  | black_parent_right {plow pupp a sib}
      : RBTree_BST plow (.el a) sib
      → between plow a pupp
      → Ancestor_BST plow pupp (.el a) pupp (.black_parent .right a sib)

-- Since we're only interested in inserting into full trees, we assume that the outer bounds
-- of an ancestry are .min and .max.
-- This means we don't specify our insertion algorithm as precisely as we could (we can't reason
-- about inserting into trees with specific bounds), but it reduces a lot of clutter.
inductive Ancestry_BST : (low upp : WithBounds α) → Ancestry α c k → Prop where
  | root : Ancestry_BST .min .max .root
  | parent (plow pupp anc ancs)
      : Ancestor_BST plow pupp low upp anc
      → Ancestry_BST plow pupp ancs
      → Ancestry_BST low upp (.parent anc ancs)

-- Instead of working with an upper and a lower bound here direclty, we track the
-- value that we plan to insert and ensure it can be inserted at the given location.
inductive InsertionPoint_BST (ai : α) : InsertionPoint α → Prop where
  | already_present : InsertionPoint_BST ai .already_present
  | insert_at : between low ai upp → Ancestry_BST low upp ancs → InsertionPoint_BST ai (.insert_at ancs)
