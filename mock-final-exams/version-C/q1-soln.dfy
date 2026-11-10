/* MOCK FINAL EXAM 2026 (Version C): Question 1.  -- SOLUTIONS

   7 marks in total

   All students to answer all questions.

   Replace /* YOUR WORK GOES HERE */ comments with your
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to
   have a proof.  Remember to include the {} and any
   necessary proof-steps within the braces !

   Topics: option types, dictionaries (association lists),
   lookup / insert / remove, lemmas about them.
*/

datatype option<V> = None | Some(value: V)

datatype dict = Empty | Entry(key: int, data: string, rest: dict)

/* 1A.
   Define lookup(k, d): Some(v) for the FIRST entry in d with
   key k, or None if there is no such entry.

   1 mark
*/
function lookup(k: int, d: dict) : option<string>
{
  match d
  case Empty => None
  case Entry(k2, v, rest) => if k == k2 then Some(v) else lookup(k, rest)
}

/* 1B.
   Define insert(k, v, d), which adds the binding k |-> v so
   that it shadows any older binding for k.

   1 mark
*/
function insert(k: int, v: string, d: dict) : dict
{
  Entry(k, v, d)
}

/* 1C.
   State and prove the testing lemma that looking up 2 in
   insert(1, "a", insert(2, "b", Empty)) gives Some("b").

   1 mark
*/
lemma lookup_test()
  ensures lookup(2, insert(1, "a", insert(2, "b", Empty))) == Some("b") {}

/* 1D.
   State and prove that after inserting k |-> v, looking up k
   gives Some(v).

   1 mark
*/
lemma lookup_insert_same(k: int, v: string, d: dict)
  ensures lookup(k, insert(k, v, d)) == Some(v) {}

/* 1E.
   State and prove that inserting a binding for k2 does not
   change the result of looking up a DIFFERENT key k1.

   1 mark
*/
lemma lookup_insert_other(k1: int, k2: int, v: string, d: dict)
  requires k1 != k2
  ensures lookup(k1, insert(k2, v, d)) == lookup(k1, d) {}

/* 1F.
   Define remove(k, d), which deletes EVERY entry with key k
   (keeping the others in order).  Then state and prove that
   looking up k after remove(k, d) gives None.

   2 marks
*/
function remove(k: int, d: dict) : dict
{
  match d
  case Empty => Empty
  case Entry(k2, v, rest) =>
    if k == k2 then remove(k, rest) else Entry(k2, v, remove(k, rest))
}

lemma lookup_remove(k: int, d: dict)
  ensures lookup(k, remove(k, d)) == None {}
