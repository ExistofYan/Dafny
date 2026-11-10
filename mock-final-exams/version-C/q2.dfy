/* MOCK FINAL EXAM 2026 (Version C): Question 2.

   8 marks in total

   All students to answer all questions.

   Replace /* YOUR WORK GOES HERE */ comments with your
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to
   have a proof.  Remember to include the {} and any
   necessary proof-steps within the braces !

   Topics: binary search trees, tree induction, ghost
   predicates with forall, proving a forall with a forall
   STATEMENT, using an earlier lemma inside a proof.
*/

datatype tree = Leaf | Node(left: tree, key: int, right: tree)

/* 2A.
   Define contains(t, x): true exactly when x is a key
   ANYWHERE in t (search both subtrees; do not assume t is
   ordered).

   1 mark
*/
predicate contains(t: tree, x: int)
{
  /* YOUR WORK GOES HERE */
}

/* 2B.
   Define bstInsert(t, x), the usual binary-search-tree
   insertion: go left if x is smaller than the key, right if
   larger, and leave the tree unchanged if x is already the key.

   1 mark
*/
function bstInsert(t: tree, x: int) : tree
{
  /* YOUR WORK GOES HERE */
}

/* 2C.
   State and prove the testing lemma that after inserting 5
   and then 3 into an empty tree, the tree contains 3.

   1 mark
*/
/* YOUR WORK GOES HERE */

/* 2D.
   State and prove that y is in bstInsert(t, x) if and only if
   y was already in t or y == x.

   2 marks
*/
/* YOUR WORK GOES HERE */

/* 2E.
   bst(t) below says that t is a binary search tree.  Prove that
   bstInsert preserves this property.  You will need 2D, and
   forall statements to establish the forall parts of bst.

   3 marks
*/
ghost predicate bst(t: tree)
{
  match t
  case Leaf => true
  case Node(l, k, r) =>
    bst(l) && bst(r) &&
    (forall y :: contains(l, y) ==> y < k) &&
    (forall y :: contains(r, y) ==> y > k)
}

lemma bst_insert(t: tree, x: int)
  requires bst(t)
  ensures bst(bstInsert(t, x))
{
  /* YOUR WORK GOES HERE */
}
