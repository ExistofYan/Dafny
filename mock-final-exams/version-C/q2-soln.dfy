/* MOCK FINAL EXAM 2026 (Version C): Question 2.  -- SOLUTIONS

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
  match t
  case Leaf => false
  case Node(l, k, r) => x == k || contains(l, x) || contains(r, x)
}

/* 2B.
   Define bstInsert(t, x), the usual binary-search-tree
   insertion: go left if x is smaller than the key, right if
   larger, and leave the tree unchanged if x is already the key.

   1 mark
*/
function bstInsert(t: tree, x: int) : tree
{
  match t
  case Leaf => Node(Leaf, x, Leaf)
  case Node(l, k, r) =>
    if x < k then Node(bstInsert(l, x), k, r)
    else if x > k then Node(l, k, bstInsert(r, x))
    else t
}

/* 2C.
   State and prove the testing lemma that after inserting 5
   and then 3 into an empty tree, the tree contains 3.

   1 mark
*/
lemma bstInsert_test()
  ensures contains(bstInsert(bstInsert(Leaf, 5), 3), 3) {}

/* 2D.
   State and prove that y is in bstInsert(t, x) if and only if
   y was already in t or y == x.

   2 marks
*/
lemma contains_insert(t: tree, x: int, y: int)
  ensures contains(bstInsert(t, x), y) <==> contains(t, y) || y == x
{}

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
  match t
  case Leaf => {}
  case Node(l, k, r) => {
    if x < k {
      bst_insert(l, x);
      forall y | contains(bstInsert(l, x), y) ensures y < k {
        contains_insert(l, x, y);
      }
    } else if x > k {
      bst_insert(r, x);
      forall y | contains(bstInsert(r, x), y) ensures y > k {
        contains_insert(r, x, y);
      }
    }
  }
}
