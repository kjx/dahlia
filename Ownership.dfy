//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Dave clark ownerhsip sketch.
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

function owners(o : Object) : set<Object> { o.AMFO }


///inside or equal to
predicate inside(part : Object, whole : Object) : (rv : bool)
 // reads part, whole 
 {
// || whole.region.World?
  || part == whole
  || whole in part.AMFO
}

predicate outside(part : Object, whole : Object) : (rv : bool)
  { not(inside(part,whole)) }

///inside BUT NOT equal to
predicate strictlyInside(part : Object, whole : Object) : (rv : bool)
 // reads part, whole 
 {
// || whole.region.World?
  && part != whole
  && whole in part.AMFO
}



lemma InsideIsHeap(part : Object, whole : Object) 
   requires part.Ready()
   requires inside(part, whole)
   requires part != whole 
   ensures  part.region.Heap?
{
  //////reveal part.Ready();

}




///kjx 1.16 am Mon 27 May
///this also says: make world and owner, yesm bvut have ONLY ONE suchobject
///put WORLD in every object's ownershiplist (AMFO alongwith itself)
///this this is simply t.owner in f.AMFO

///WORLD could be an object 
lemma {:NOTonly} PointingLemma(f : Object, t : Object) 
  requires || t.region.World? 
           || (&& t.region.Heap? 
               && t.region.owner in (f.AMFO + {f}))
  ensures refOK(f,t)            
{}


///OUTGOING requires something like 
///if T is outside f (or outside F.owner)???
///the T must be on f's putoing list. 
///needs to be consistent up the hierarcy 
  





predicate refOK(f : Object, t : Object) : (rv : bool)
  // requires ownersOK(f,os) //isthere an AMFO verison of this? //this is snow the AMFO version
  // requires ownersOK(t,os)
  // reads f, t//, t`region
  // reads if (t.region.Heap?) then {t.region.owner} else {}
{  t.region.World? || (t.region.Heap? && inside(f,t.region.owner))
}


lemma WorldCanFuckItself(f : Object, t : Object)
  requires f.region.World?
  requires refOK(f,t)
{ 
  if (t.region.World?) { assert refOK(f,t); return;}
  if (t.region.Heap? && t.region.owner == f)  { assert refOK(f,t); return;}
}

//pretty nice version...
lemma {:Mon18Dec} {:timeLimit 30}  {:vcs_split_on_every_assert} transitiveInside(a : Object, b : Object, c : Object)
  // requires a != b
  // requires b != c
  // requires c != a
  //requires a.Valid() && b.Valid() && c.Valid()
  //requires forall o <- {a, b, c} :: o.region.Heap?
  requires a.Ready() && b.Ready() && c.Ready()
  requires inside(a,b)
  requires inside(b,c)
  ensures  inside(a,c)
{
  //////reveal Object.Ready();
}







//////////////////////////////////////////////////////////////////////////////
/// ownership test lemmas / ownershiop accessors...
//////////////////////////////////////////////////////////////////////////////

//this one is kind of odd, really...
lemma ownerNOTInside(a : Object, b : Object, c : Object)
  // requires a != b
  // requires b != c
  // requires c != a
    requires a.Ready() && b.Ready() && c.Ready()
    requires a.Valid() && b.Valid() && c.Valid()
  //requires forall o <- {a, b, c} :: o.region.Heap?

  requires a.region.Heap? && a.region.owner == b
  // requires a.region.Heap? && (b in a.AMFO) //b is an ownwer of a?
  requires c !in a.extra
  //requires c !in a.AMFO
  requires not(inside(b,c))
  requires not(inside(c,b))
  ensures  not(inside(a,c))
{}

lemma insideMyDirectOwner(a : Object)
  requires a.Ready() && a.Valid()
  requires a.region.Heap? 
  ensures  inside(a,a.region.owner)
{}



//a truncated eversiversion of transitiveinside
//that's sticking around for auld lang syne?
//a is inside some object c
//a != c 
//b is a's direct owner
//b != c
//b is insidde c
lemma {:isolate_assertions} insideSomeIndirectOwner(a : Object, b : Object, c : Object)
  requires a.Ready() && a.Valid()  //not the rest?
  requires a.region.Heap? && b.region.Heap?
  requires a != b && a != c && b != c  //not sure we need all of these...
  requires inside(a,c)
  requires b == a.region.owner
  requires c !in a.AMFO
  ensures  inside(b,c)
{
  if (not(inside(b,c)))   //proof by contradiction...
     {
      assert not( b.AMFO >= c.AMFO );   //not entirely sure about all this but...
      assert c !in b.AMFO;
      assert a.AMFO == b.AMFO + a.extra + {a};
      assert c !in a.AMFO;
      assert not( a.AMFO >= c.AMFO );
      assert not(inside(a,c));
      assert false;
     }
   assert inside(b,c);
}


//Hmm is this enough.insideToAMFO
//Yes this verifies!!!
function ownersBetween(part : Object, whole : Object) : (rv : set<Object>)
 requires part.Ready()
 requires whole.Ready()
 requires inside(part,whole)
 reads part.ValidReadSet() + whole.ValidReadSet()
 ensures inside(part, whole)
 ensures forall r <- rv :: inside(part, r)
 ensures forall r <- rv :: inside(r, whole)
{
 set o <- part.AMFO | inside(o,whole)
}

