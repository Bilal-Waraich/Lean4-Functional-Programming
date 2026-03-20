import Exercises.Problems
import Exercises.Autograder

variable {α : Type} [LinearOrder α]

def ex01 : {node : RBTree α c k} → (hlow : low' ≤ low) → (hupp : upp ≤ upp') → RBTree_BST low upp node → RBTree_BST low' upp' node := RBTree_BST.change_bounds
def ex02 : {ancs : Ancestry α c k} → {node : RBTree α c k} → Ancestry_BST low upp ancs → RBTree_BST low upp node → RBRoot_BST (ancs.rebuild node) := Ancestry.rebuild_respects_BST
def ex03 : {node : RBTree α .red k} → RBTree_BST low upp node → RBTree_BST low upp node.make_black := make_black_respects_BST
def ex04 : {node : RBTree α c k} → RBTree_BST low upp node → RBRoot_BST node.to_root := to_root_respects_BST
def ex05 : {anc : Ancestor α .black pk c k} → Ancestor_BST plow pupp low upp anc → Ancestor_BST plow pupp low upp anc.allow_red := allow_red_respects_BST
def ex06 : {anc : Ancestry α .black k} → {node : RBTree α .red k} → Ancestry_BST low upp anc → RBTree_BST low upp node → RBRoot_BST (anc.rebuild_and_fix node) := rebuild_and_fix_respects_BST
def ex07 : {node : RBTree α c k} → between low ai upp → RBTree_BST low upp node → Ancestry_BST low upp ancs → InsertionPoint_BST ai (node.find_insertion_point_rec ai ancs) := find_insertion_point_rec_respects_BST
def ex08 : {node : RBRoot α} → RBRoot_BST node → InsertionPoint_BST ai (node.find_root_insertion_point ai) := find_root_insertion_point_respects_BST
def ex09 : {node : RBRoot α} → RBRoot_BST node → RBRoot_BST (node.insert ai) := RBRoot_BST.insert_preserves_BST

#print_grade_results ex01 ex02 ex03 ex04 ex05 ex06 ex07 ex08 ex09
