//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Dave clark ownerhsip sketch.
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// function owners(o : Object) : set<Object>
// // deprecated
//  //all o's owners except o itself
//  { o.allExternalOwners() } //should this be a function on objects? - 'tis now

///inside or equal to
predicate inside(part : Object, whole : Object) : (rv : bool)
  ensures rv <==> (whole.AMFO <= part.AMFO)
  {
    part.AMFO >= whole.AMFO
  }

predicate outside(part : Object, whole : Object) : (rv : bool)
  ensures rv <==> (not(inside(part,whole)))
  ensures rv <==> (not(part.AMFO >= whole.AMFO))
  {
    not(inside(part,whole))
  }


predicate strictlyInside(part : Object, whole : Object) : (rv : bool)
 //inside BUT NOT equal to
 // reads part, whole
 {
// || whole.region.World?
  && part != whole
  && whole.AMFO <= part.AMFO
 }

lemma reallyStrictlyInside(part : Object, whole : Object)
 requires part.Ready()
 requires whole.Ready()
 ensures strictlyInside(part, whole) == (part.AMFO > whole.AMFO)
 {
   assert strictlyInside(part, whole) == ((part != whole) && (whole.AMFO <= part.AMFO));
   assert strictlyInside(part, whole) == ((part != whole) && (part.AMFO >= whole.AMFO));
   AXIOMAMFOS(part,whole);
   assert ((part != whole) <==> (part.AMFO != whole.AMFO));
 }

predicate directlyInside(part : Object, whole : Object) : (rv : bool)
 {
   whole.AMFO == part.allExternalOwners()  //?yeah - what if there are stack owners around?
 }

lemma reallyDirectlyInside(part : Object, whole : Object)
 ensures directlyInside(part, whole) == (part.AMFX == whole.AMFO) {}



predicate directlyBounded(part : Object, bound : Object) : (rv : bool)
 {
   part.AMFB  == bound.AMFO //?yeah - what if there are stack owners around?
   // or part.bound == bound ??
 }

 predicate insideOwner(part : Object, whole : Object) : (rv : bool)
 // is part inside whole's *Owners*, i.e. a peer or inside a peer?
 // reads part, whole
  ensures rv <==> (part.AMFO >= whole.allExternalOwners())
  ensures rv <==> (whole.allExternalOwners() <= part.AMFO)
  ensures rv <==> (ownerInsideOwner(part.AMFO, whole.allExternalOwners()))
 {
   part.AMFO >= whole.AMFX
 //  part.AMFO >= whole.allExternalOwners()
//    whole.allExternalOwners() <= part.AMFO
 }

 predicate boundInsideOwner(part : Object, whole : Object) : (rv : bool)
 // is part's bound inside whole's *Owners*?
 // reads part, whole
  ensures rv <==> (part.AMFB >= whole.allExternalOwners())
  ensures rv <==> (whole.allExternalOwners() <= part.AMFB)
  ensures rv <==> (ownerInsideOwner(part.AMFB, whole.allExternalOwners()))
 {
  part.AMFB >= whole.allExternalOwners()
//    whole.allExternalOwners() <= part.AMFB
 }



lemma InsideOwnerVsBound(part : Object, whole : Object, context : set<Object>)
  requires COK(part, context)
  requires COK(whole, context)
  requires boundInsideOwner(part, whole)
  ensures  insideOwner(part, whole)
   {
    reveal COK();
   }

lemma Inside3(a : Object, b : Object, c : Object)
  requires inside(a,b)
  requires inside(b,c)
  ensures  inside(a,c)
{}


//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////
// generalised verisons as required by "cut" -- hmm I feel unconvined by this
//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

predicate ownerInsideOwner(partO : Owner, wholeO : Owner)
{
 partO >= wholeO
}


predicate ownerInsideOwnerInsideOwner(partO : Owner, midO : Owner, wholeO : Owner)
{
//  forall p <- partO :: exists w <- wholeO :: inside(p, w)
 partO >= midO >= wholeO
}


lemma BLURareCUNTS(partO : Owner, wholeO : Owner)
  requires ownerInsideOwner(partO, wholeO)
  // ensures  not(partO !! wholeO)
  // ensures  flattenAMFOs(partO) >= flattenAMFOs(wholeO)
{

}

lemma InsideToOwners(part : Object, whole : Object)
 requires part.Ready()
 requires whole.Ready()
 ensures inside(part,whole) == ownerInsideOwner(part.AMFO, whole.AMFO)
 ensures insideOwner(part,whole) == ownerInsideOwner(part.AMFO,whole.allExternalOwners())
 ensures inside(part,whole) ==> insideOwner(part,whole)
{

}


//pretty nice version... {:Mon18Dec}
lemma transitiveInsideOwners(a : Owner, b : Owner, c : Owner)
  // requires a != b
  // requires b != c
  // requires c != a
  //requires a.Ready() && b.Ready() && c.Ready()
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

lemma PointingLemmaOld(f : Object, t : Object)
  requires t.owner <= (f.AMFB)
  requires boundInsideOwner(f, t)
  ensures refOK(f,t)
{
  //KJX is this right?4

  assert t.allExternalOwners() <= f.AMFB;
  assert refOK(f,t);
}


lemma PointingLemma(f : Object, t : Object)
  requires boundInsideOwner(f, t)
//    requires ownerInsideOwner(t.AMFO,  f.bound)
  ensures  refOK(f,t)
{
}


///OUTGOING requires something like
///if T is outside f (or outside F.owner)???
///the T must be on f's putoing list.
///needs to be consistent up the hierarcy


// lemma MOREreffing(f : Object, t : Object)
//   ensures(refOK(f,t) <==> (boundInsideOwner(f, t) || (f==t)))
// {}


predicate OLDERrefOK(f : Object, t : Object) : (rv : bool)
  // requires ownersOK(f,os) //isthere an AMFO verison of this? //this is snow the AMFO version
  // requires ownersOK(t,os)
  // reads f, t//, t`region
  // reads if (t.region.Heap?) then {t.region.owner} else {}
{  insideOwner(f,t) }


predicate oldishRefOK(f : Object, t : Object) : (rv : bool) //moved 23Dec2024
  { boundInsideOwner(f,t) || directlyInside(t,f) }

predicate   oldyRefOK(f : Object, t : Object) : (rv : bool)
  // requires ownersOK(f,os) //isthere an AMFO verison of this? //this is snow the AMFO version
  // requires ownersOK(t,os)
  // reads f, t//, t`region
    // reads if (t.region.Heap?) then {t.region.owner} else {}
  // ensures rv <==> (boundInsideOwner(f,t) || (f == t))
{ // && insideOwner(f,t)
  // ownerInsideOwner(f.AMFO,t.allExternalOwners())
  //ownerInsideOwner(part.AMFO, whole.allExternalOwners())
  //  ownerInsideOwner(f.bound,t.allExternalOwners())
  || (f==t)
  || boundInsideOwner(f,t)
  || directlyInside(t,f)
}


lemma WorldCanFuckItself(f : Object, t : Object)
//we don't really have "world" any more but if we did...
  requires f.AMFO == {f}
  requires refOK(f,t)
{
  if (t.AMFO == {}) { assert refOK(f,t); return;}
  if (t.allExternalOwners() == {f})  { assert refOK(f,t); return;}
}

//pretty nice version... {:Mon18Dec 2023}
lemma transitiveInside(a : Object, b : Object, c : Object)
  // requires a != b
  // requires b != c
  // requires c != a
  //requires a.Ready() && b.Ready() && c.Ready()
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
 requires forall p <- part.AMFO :: inside(part, p)//KJX WATCH OUT FOR THIS 31 DEC 2024
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

  requires a.Ready() && b.Ready()
  requires forall o <- c :: o.Ready()

//  ensures (a in b.AMFO) ==> (b !in a.AMFO)
  requires a  in b.AMFO
  ensures  b !in a.AMFO
{
 reveal COK(), CallOK();
 assert COK(a,c);
 assert COK(b,c);
 assert CallOK(c);

a.AMFOsisAMFOs4();
b.AMFOsisAMFOs4();

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

// all thsi shit commented out
// because collectAllOwners over in SuperKlon.dfy does the same thing
// only far far better!
//
// lemma AMFOsmaller(a : Object)
//   requires a.Ready() && a.Valid()
//   ensures  forall oo <- a.AMFX :: strictlyInside(a,oo)
// {}
//
// function AllMyConcievableOwners(a : Object) : (amco : Owner)
//   decreases a.AMFO
//   requires a.Ready()
// //ensures amco == a.AMFX
//   ensures a !in amco
//   ensures amco <= a.AMFX
//   {
//     assert a.Ready();
//     a.ReadyGetsOwnersValid();
//     assert a.OwnersValid();
//     assert forall oo <- a.AMFX :: a.AMFO > oo.AMFO;
//     assert forall oo <- a.AMFX :: oo.Ready();
// //    set oo <- a.AMFX, ooo <- (AllMyConcievableOwners(oo) + {oo}) :: ooo
//     set oo <- a.AMFX, ooo <- (AllMyConcievableOwners(oo) + {oo}) :: ooo
//   }
//
// lemma AllMyConcievableOwnersAreFUCKINGFlat1(a : Object)
//   decreases a.AMFO
//   requires a.Ready()
//   ensures  AllMyConcievableOwners(a) <= a.AMFO
//   ensures AllMyConcievableOwners(a) <= a.AMFX
//   {}
//
// lemma AllMyConcievableOwnersAreFUCKINGFlat2(a : Object)
//   decreases a.AMFO
//   requires a.Ready()
//   // ensures  AllMyConcievableOwners(a) <= a.AMFO
//    ensures AllMyConcievableOwners(a) >= a.AMFX
//   {
//   //  assert forall oo <- a.AMFX :: a in AllMyConcievableOwners(a);
//
//   if (AllMyConcievableOwners(a) >= a.AMFX)
//    { assert true;
//      return;
//    } else {
//      assert not(AllMyConcievableOwners(a) >= a.AMFX);
//      assert    (AllMyConcievableOwners(a) <  a.AMFX);
//      assert exists x <- a.AMFX :: x !in AllMyConcievableOwners(a);
//      assert exists x <- a.AMFX :: (x !in (set oo <- a.AMFX :: oo));
//      assert exists x <- a.AMFX :: (x !in
//               (set oo <- a.AMFX, ooo <- (AllMyConcievableOwners(oo) + {oo}) :: ooo));
//      assert {:contradiction} forall x <- a.AMFX :: (x in
//               (set oo <- a.AMFX, ooo <- (AllMyConcievableOwners(oo) + {oo}) :: ooo));
//      assert {:contradiction} false;
//      return;
//    }
//   }
//
// lemma AllMyConcievableOwnersAreOKInThisKlown(a : Object, m : Klon, allMyConcievableOwnersExceptMe : Owner)
//   requires a.Ready()
//   requires allMyConcievableOwnersExceptMe == (AllMyConcievableOwners(a) - {a})
//   requires m.ownersInKlown(a)
//   ensures  allMyConcievableOwnersExceptMe <= m.m.Keys
// {}

lemma AMFXabreOK(a : Object, m : Klon)
  decreases a.AMFO

  requires  a.Ready()
  requires  m.ownersInKlown(a)
  ensures   forall oo <- a.AMFX :: m.ownersInKlown(oo)
{}

lemma {:verify false} AMFOSareOK(a : Object, context : set<Object>)
//this DOES NOT WORK - owner are READY but not necessarily VALID
  decreases a.AMFO

  requires COK(a,context)
  ensures  forall oo <- a.AMFO :: oo.AMFO <= context
  ensures  forall oo <- a.AMFO :: COK(oo, context)
  ensures  forall oo <- a.AMFO :: CallOK(oo.AMFO, context)
  //CallOK(a.AMFO, context)
{
  reveal COK(), CallOK();

  assert a.Ready();
  forall oo <- a.AMFO ensures  COK(oo, context) //by
  {
   assert oo.Ready();
   assert oo in context;
   assert oo.Valid() by {
     assert oo.OwnersValid();
     assert oo.AllFieldsAreDeclared();   //doesnt work
     assert oo.AllFieldsContentsConsistentWithTheirDeclaration(); //doesnto work
   }
   assert (a.AllOutgoingReferencesAreOwnership(context));
   assert (a.AllOwnersAreWithinThisHeap(context));

   assert COK(oo, context);
  }
}

//////////////////////////////////////////////////////////////////////////////
/// refOK - in from spike
//////////////////////////////////////////////////////////////////////////////


predicate refBI(f : Object, t : Object) {f.AMFB >= t.AMFX}
predicate refDI(f : Object, t : Object) {f.AMFO == t.AMFX}
predicate refOK(f : Object, t : Object) {(f==t) || refBI(f,t) || refDI(f,t)}

predicate fefBI(f : Object, t : Object) {flatten(f.bound) >= flatten(t.owner)}


///// lemmata

lemma canWeSimplify1(f : Object, t : Object, context : set<Object>, m : Klon)
 //no we can't :-(
  requires m.boundsNestingOK(f, context)
  requires m.boundsNestingOK(t, context)
  ensures  refOK(f,t) == ((f==t) || refBI(f,t) || refDI(f,t))
  ensures  refOK(f,t) == ((f==t) || (f.AMFB >= t.AMFX) || (f.AMFO == t.AMFX))
  //ensures  refOK(f,t) == ((f.AMFO == t.AMFO) || (f.AMFB >= t.AMFX) || (f.AMFO == t.AMFX))
{}

lemma COKandReadyGetsAMFOandAMFX(f : Object, context : set<Object>, m : Klon)
    requires COK(f,context)
    requires f.Ready()
    ensures  (f.AMFO - f.AMFX) == {f}
    {}

lemma EmptyBoundMeansNoOutgoingReferences(f : Object, t : Object, context : set<Object>, m : Klon)
  //if the "from" object's bound is "empty {}" i.e top T - then there can be NO outgoing revernecs
  //(so that is full alias encqpsuation aka a capsule)
  //(well almost no outgoing references, assuming the target doesn't have owner {}.  And no real object should!)
  requires f.Ready()
  requires t.Ready()
  requires m.boundsNestingOK(f, context)
  requires m.boundsNestingOK(t, context)
  requires not(f==t)
  requires not((f.AMFO == t.AMFX))
  // ensures  refOK(f,t) == refBI(f,t) == (f.AMFB >= t.AMFX)
  requires f.AMFB == {} //FROM bounds is nothing
  requires t.AMFX >  {} //to onwer is more than nothing :-)
  // ensures  refOK(f,t) == refBI(f,t) == (f.AMFB >= t.AMFX)
  // ensures  refOK(f,t) == refBI(f,t) == ({} >= t.AMFX)
  ensures  not(refOK(f,t))
{}
