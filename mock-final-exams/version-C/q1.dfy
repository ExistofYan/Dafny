/* MOCK FINAL EXAM 2026 (Version C): Question 1.

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
  /* YOUR WORK GOES HERE */
  match d case Empty => None
  case Entry(key,data,r) => if key == k then Some(data) else lookup(k,r) 
}

/* 1B.
   Define insert(k, v, d), which adds the binding k |-> v so
   that it shadows any older binding for k.

   1 mark
*/
function insert(k: int, v: string, d: dict) : dict
{
  /* YOUR WORK GOES HERE */
  match d case Empty => Entry(k,v,Empty)
  case Entry(key,data,rest) => if key == k then Entry(k,v,rest) else Entry(key,data,insert(k,v,rest))
}

/* 1C.
   State and prove the testing lemma that looking up 2 in
   insert(1, "a", insert(2, "b", Empty)) gives Some("b").

   1 mark
*/
/* YOUR WORK GOES HERE */
lemma lokkingup_insert()
ensures lookup(2,insert(1,"a",insert(2, "b", Empty))) == Some("b")
{}

/* 1D.
   State and prove that after inserting k |-> v, looking up k
   gives Some(v).

   1 mark
*/
/* YOUR WORK GOES HERE */

/* 1E.
   State and prove that inserting a binding for k2 does not
   change the result of looking up a DIFFERENT key k1.

   1 mark
*/
/* YOUR WORK GOES HERE */

/* 1F.
   Define remove(k, d), which deletes EVERY entry with key k
   (keeping the others in order).  Then state and prove that
   looking up k after remove(k, d) gives None.

   2 marks
*/
function remove(k: int, d: dict) : dict
{
  /* YOUR WORK GOES HERE */
  match d case Empty => Empty
  case Entry(key,data,rest) => if key == k then rest else Entry(key,data,remove(k,rest))
}

/* YOUR WORK GOES HERE */
