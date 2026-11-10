/* MOCK FINAL EXAM 2026 (Version A): Question 3.

   8 marks in total

   All students to answer all questions.

   Replace /* YOUR WORK GOES HERE */ comments with your
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to
   have a proof.  Remember to include the {} and any
   necessary proof-steps within the braces !

   Topics: binary trees, tree recursion, tree induction,
   {:induction false} (you must make the inductive calls
   yourself), auxiliary lemmas about append/length.
*/

include "core-list.dfy"

datatype tree = Leaf | Node(left: tree, data: int, right: tree)

/* 3A.
   Define size(t), the number of Nodes in t.

   1 mark
*/
function size(t: tree) : nat
{
  /* YOUR WORK GOES HERE */
}

/* 3B.
   Define mirror(t), which swaps the left and right subtrees
   of every Node.

   1 mark
*/
function mirror(t: tree) : tree
{
  /* YOUR WORK GOES HERE */
}

/* 3C.
   Define sumTree(t), the sum of all the values in t.

   1 mark
*/
function sumTree(t: tree) : int
{
  /* YOUR WORK GOES HERE */
}

/* 3D.
   State and prove that mirroring a tree does not change
   its sum.

   1 mark
*/
/* YOUR WORK GOES HERE */

/* 3E.
   Define inorder(t), the list of values in t in left-to-right
   (in-order) order.  Use append from core-list.dfy.

   1 mark
*/
function inorder(t: tree) : ilist
{
  /* YOUR WORK GOES HERE */
}

/* 3F.
   State and prove that the length of inorder(t) is size(t).

   Your main lemma MUST carry the {:induction false} attribute,
   so you have to write the inductive calls yourself.  You will
   also need to state and prove an auxiliary lemma about the
   length of an append.

   3 marks
*/
/* YOUR WORK GOES HERE */
