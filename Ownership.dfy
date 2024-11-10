//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Dave clark ownerhsip sketch.
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

function owners(o : Object) : set<Object>
// deprecated
 //all o's owners except o itself
 { o.allExternalOwners() } //should this be a function on objects? - 'tis now

///inside or equal to
predicate inside(part : Object, whole : Object) : (rv : bool)
 // reads part, whole 
 {
   whole.AMFO <= part.AMFO
 }

predicate outside(part : Object, whole : Object) : (rv : bool)
  { not(inside(part,whole)) }

///inside BUT NOT equal to
predicate strictlyInside(part : Object, whole : Object) : (rv : bool)
 // reads part, whole 
 {
// || whole.region.World?
  && part != whole
  && whole.AMFO <= part.AMFO
 }

predicate directlyInside(part : Object, whole : Object) : (rv : bool)
 {
   whole.AMFO == part.allExternalOwners()  //?
 }

 predicate insideOwner(part : Object, whole : Object) : (rv : bool)
 // is part inside whole's *Owners*, i.e. a peer or inside a peer?
 // reads part, whole 
 {
   whole.allExternalOwners() <= part.AMFO
 }



//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////
// generalised verisons as required by "cut" -- hmm I feel unconvined by this
////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////

predicate ownerInsideOwner(partO : Owner, wholeO : Owner) 
{
  forall p <- partO :: exists w <- wholeO :: inside(p, w)
}

lemma BLURareCUNTS(partO : Owner, wholeO : Owner) 
  requires ownerInsideOwner(partO, wholeO) 
  ensures  not(partO !! wholeO)
  ensures  flattenAMFOs(partO) >= flattenAMFOs(wholeO) 
{

}

lemma InsideToOwners(part : Object, whole : Object)
 ensures inside(part,whole) == ownerInsideOwner({part}, {whole})
{

}


//pretty nice version... {:Mon18Dec} 
lemma transitiveInsideOwners(a : Owner, b : Owner, c : Owner)
  // requires a != b
  // requires b != c
  // requires c != a
  //requires a.Valid() && b.Valid() && c.Valid()
  //requires forall o <- {a, b, c} :: o.region.Heap?
  //equires a.Ready() && b.Ready() && c.Ready()

  requires forall o <- (a + b + c) :: o.Ready()
  requires ownerInsideOwner(a,b)
  requires ownerInsideOwner(b,c)
  ensures  ownerInsideOwner(a,c)
{}

///kjx 1.16 am Mon 27 May 2024
///this also says: make world and owner, yesm bvut have ONLY ONE suchobject
///put WORLD in every object's ownershiplist (AMFO alongwith itself)
///this this is simply t.owner in f.AMFO

///WORLD could be an object 
lemma PointingLemma(f : Object, t : Object) 
//  requires t.owner <= (f.AMFO)
  requires insideOwner(f, t)
  ensures refOK(f,t)            
{
  //KJX is this right?

  assert t.allExternalOwners() <= f.AMFO;
  assert refOK(f,t);
}


///OUTGOING requires something like 
///if T is outside f (or outside F.owner)???
///the T must be on f's putoing list. 
///needs to be consistent up the hierarcy 
  

lemma MOREreffing(f : Object, t : Object)
  ensures(refOK(f,t) ==> insideOwner(f, t))
{}



predicate refOK(f : Object, t : Object) : (rv : bool)
  // requires ownersOK(f,os) //isthere an AMFO verison of this? //this is snow the AMFO version
  // requires ownersOK(t,os)
  // reads f, t//, t`region
  // reads if (t.region.Heap?) then {t.region.owner} else {}
{  insideOwner(f,t) }


lemma WorldCanFuckItself(f : Object, t : Object)
//we don't really have "world" any more but if we did...
  requires f.AMFO == {f}
  requires refOK(f,t)
{ 
  if (t.AMFO == {}) { assert refOK(f,t); return;}
  if (t.allExternalOwners() == {f})  { assert refOK(f,t); return;}
}

//pretty nice version... {:Mon18Dec} 
lemma transitiveInside(a : Object, b : Object, c : Object)
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

//  requires a.region.Heap? && a.region.owner == b
  requires directlyInside(a,b)
  // requires a.region.Heap? && (b in a.AMFO) //b is an ownwer of a?
  //requires c !in a.AMFO
  requires not(inside(b,c))
  requires not(inside(c,b))
  ensures  not(inside(a,c))
{}

lemma insideMyDirectOwner(a : Object)
  requires a.Ready() && a.Valid()
  ensures  forall oo <- a.AMFO :: inside(a, oo)
{}



//a truncated eversiversion of transitiveinside
//that's sticking around for auld lang syne?
//a is inside some object c
//a != c 
//b is a's direct owner
//b != c
//b is insidde c
lemma insideSomeIndirectOwner(a : Object, b : Object, c : Object)
  requires a.Ready() && a.Valid()  //not the rest?
  requires a != b && a != c && b != c  //not sure we need all of these...
  requires inside(a,c)
  requires inside(b,a)
  requires c !in a.AMFO
  ensures  inside(b,c)
{
  if (not(inside(b,c)))   //proof by contradiction...
     {
      assert {:contradiction}  not( b.AMFO >= c.AMFO );   //not entirely sure about all this but...
      assert {:contradiction} c !in b.AMFO;
      assert {:contradiction} a.AMFO == b.AMFO + {a};
      assert {:contradiction} c !in a.AMFO;
      assert {:contradiction} not( a.AMFO >= c.AMFO );
      assert {:contradiction} not(inside(a,c));
      assert {:contradiction} false;
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



lemma ownershipIsMonotonic(a : Object, b : Object, c : set<Object>) 
  requires a != b //oops!`
  requires a in c
  requires b in c
  requires COK(a,c)
  requires COK(b,c)
  requires CallOK(c)

//  ensures (a in b.AMFO) ==> (b !in a.AMFO)
  requires a  in b.AMFO
  ensures  b !in a.AMFO   
{
 reveal COK(), CallOK();
 assert COK(a,c);  
 assert COK(b,c); 
 assert CallOK(c);

 assert forall o <- a.AMFO :: (o != a) ==> (a.AMFO > o.AMFO);
 assert forall o <- b.AMFO :: (o != b) ==> (b.AMFO > o.AMFO);


 assert a in b.AMFO;
 

 assert b !in a.AMFO;
}


lemma OwnersAreOutsideFuckers(a : Object, o : Object)
    requires a.Ready() && a.Valid()
    requires o.Ready() && o.Valid()
    requires outside(a,o)
    ensures  forall oo <- a.allExternalOwners() ::  outside(oo, o)
    ensures  forall oo <- a.owner :: outside(oo, o)
    ensures  forall oo <- a.AMFO  :: outside(oo, o)
{
    assert a.owner <= a.AMFO;
    assert a in  a.AMFO;
    assert a !in a.owner;
}




lemma IAmInsideMyOwnersAndAMFO(a : Object, o : Object) 
    requires a.Ready() && a.Valid()
    requires o.Ready() && o.Valid()
    requires inside(a,o)
    ensures  forall oo <- a.AMFO ::  inside(a, oo)
    ensures  forall oo <- a.owner :: inside(a, oo)
{
}