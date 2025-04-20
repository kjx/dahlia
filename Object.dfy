
// datatype Region = World                         // region of immutable objects
//                   | Heap(owner : Object)         // objects allocated in heap region

type Owner = set<Object>   //still trying to devie if this sould be called Owner or Owners or Region or what!

datatype Mode =
    | Rep // owned by me
    | Peer // owned by my owner
//For all the Owner & Read "Modes" sholdn't the owner always be "self" i.e; the object containing the reernce.
    | Owned(perm : Perm) //unrestricted, Rust-style owning reference - with no borrows!
    | Loaned(perm : Perm) //owning reference, but currently there are "borrowed" references to it
    | Borrow(perm: Perm, owner: Owner, from : Object, name : string) //borrowed reference, borrowe from that object!
                                      //when one does a "stack-pop-return" into the obejct that this was borrowed from
                                      //then the Mode of the owning refernece goes from Loaned -> Owned
    | Evil //type dyanmic.  So I don't hace to do the full checks right now --- kjx 7 May 2024


datatype Perm = Read | Write | Local   ///or should these be object kinds???>  ARGH!!


    /// an earlier deprecated design!
    // | Own(perm : Owner) //unrestricted, Rust-style owning reference?
    // | Read(owner : Owner) //Rust stule ownering Readonly reference?
    //                        //IF we have move semantics, could move here from Own?
    // | ReadOwn(owner : Owner)  // I am the owner, but my contents are read-borrowed.
    // | MutOwn(owner : Owner)  // I am the owner, but my contents are mut-borrowed.
    // | LocOwn(owner : Owner)  // I am the owner, but my contents are loc-borrowed.
    // | ReadRef(owner : Owner) //

predicate AssignmentCompatible(o : Object, t : Mode, v : Object)
//can object v be assigned to a field of Mode t within object o?
{
  match t
    case Evil => true
    case Rep | Owned(_) | Loaned(_) => directlyInside(v,o) //KJX is this right  hmm?
    case Peer => v.owner == o.owner
//  case Borrow(p,b,n,f) => v.Owner == b
    case Borrow(p,b,n,f) => refOK(o,v)  //KJX not yet done
}


lemma EVILisCompatibleWithAnything(o : Object, v : Object)
  ensures AssignmentCompatible(o, Evil, v)
{}




























//////////////////////////////////////////////////////////////////////////////
//  OBJECTS
//
//I know it's perverse, but titlecase "Object" (and "Class") aren't reserved in dafny
class Object {

  const bound : Owner //movement bound - stands in for explcit owner parameters
  const AMFB  : Owner //flattened bound

  const owner : Owner//actual "dynamic" Owner owner of this object --- *XTERNAL*
  const AMFX :  Owner//flattened owner  /// aka all externeal owners

  const ntrnl : Owner//actual "dynamic" internal region onwned by this object
  const AMFO  : Owner //All MY FUCKING Owner  (aka All My Flat Owner:-)

  var   fields     : map<string,Object>//field values. uninit fields have no entries
  var   fieldModes : map<string,Mode>//Mode of each field name -  note, static! - would be statically known by any methods
    //probably also has to go to var to get to typestate. GRRR.

  var nick : string //nickname

  var randomAxMShit : bool




  constructor {:verify false} XXXmake(ks : map<string,Mode>, oo : Owner, context : set<Object>, name : string, mb : Owner := oo)

    requires ownerInsideOwner(oo,mb)

    ensures owner == oo
    ensures AMFX == flattenAMFOs(oo)
    ensures ntrnl == oo + {this}
    ensures AMFO == flattenAMFOs(oo) + {this}
    ensures bound == mb
    ensures AMFB == flattenAMFOs(mb) // + {this}  //HMM dunno if "this" should be here, but... --- ABSOLUTELY NOT!
    ensures ntrnl > owner >= bound
    ensures AMFO  > AMFX >= AMFB == flattenAMFOs(mb) >= mb

    ensures fieldModes == ks
    ensures fields == map[]

    ensures this  in AMFO
    ensures this !in owner

    ensures OwnersValid()
    ensures Ready()

    ensures (forall oo <- allExternalOwners() :: AMFO > oo.AMFO)
    ensures (forall o <-  AMFO :: inside(this, o))




    ensures COK(this, context+{this})
    ensures nick == name

    //ensures CallOK({this} + {oo}+oo.AMFO, {this} + context)

    ensures unchanged( context )
    ensures fresh(this)

    modifies {}
  {



    bound := mb;
    AMFB  := flattenAMFOs(mb);// + {this}; -- see above

    owner := oo;   ///should be owner for
    AMFX  := flattenAMFOs(oo);

    ntrnl := oo + {this};
    AMFO  := flattenAMFOs(oo) + {this};

    fieldModes := ks;
    fields := map[];
    nick := name;

    randomAxMShit := false;
    new;

  }//end XXXmake()j



constructor make(ks : map<string,Mode>, oo : Owner, context : set<Object>, name : string, mb : Owner := oo)
    requires forall o <- oo :: o.Ready()  //hmmm
    requires oo >= mb
//for OvenReady()
    requires forall o <- mb :: o.Ready()
    requires forall o <- oo :: o.Ready()
    requires forall o <- oo, ooo <- o.AMFO:: o.AMFO >= ooo.AMFO
    requires forall o <- oo, ooo <- o.AMFO :: ooo.Ready()

//end OverReady()
    requires CallOK(oo, context)
//HACK    requires CallOK(context)

    //KJX is this redundant Or wouidl it be redundat the other way around???
    // requires AllTheseOwnersAreFlatOK(oo)  //hmm? what would this mean?
    //requires CallOK({oo}+oo.AMFO, context)

    //KJX shouldn't there be some topological restriction on where or when
    //you can create new objects/contexts / regions?
    //what sgoiuld they be?
    requires ownerInsideOwner(oo,mb)

    //requires CallOK(flattenAMFOs(oo), context) //KJX is this right?
    ensures owner == oo
    ensures AMFX == flattenAMFOs(oo)
    ensures ntrnl == oo + {this}
    ensures AMFO == flattenAMFOs(oo) + {this}
    ensures bound == mb
    ensures AMFB == flattenAMFOs(mb) // + {this}  //HMM dunno if "this" should be here, but... --- ABSOLUTELY NOT!
    ensures ntrnl > owner >= bound
    ensures AMFO  > AMFX  >= AMFB == flattenAMFOs(mb) >= mb
    ensures fieldModes == ks
    ensures fields == map[]

    ensures this  in AMFO
    ensures this !in owner

    ensures OwnersValid()
    ensures Ready()

    ensures (forall oo <- allExternalOwners() :: AMFO > oo.AMFO)
    ensures (forall o <-  AMFO :: inside(this, o))




    ensures COK(this, context+{this})
    ensures nick == name
    ensures randomAxMShit == false


    //ensures CallOK({this} + {oo}+oo.AMFO, {this} + context)

    ensures unchanged( context )
    ensures fresh(this)

    modifies {}
  {



    bound := mb;
    AMFB  := flattenAMFOs(mb);

    owner := oo;
    AMFX  := flattenAMFOs(oo);

    ntrnl := oo + {this};
    AMFO  := flattenAMFOs(oo) + {this};

    fieldModes := ks;
    fields := map[];
    nick := name;

    randomAxMShit := false;
    new;

  assert this !in AMFX;

  assert AMFX == AMFO - {this};

    assert (forall b <- AMFX  :: b.Ready());
    forall b <- AMFX, c <-  b.AMFO ensures inside(b,c)  {
      assert b.Ready();
      fucked(b);
      assert inside(b,c);
    }
    assert (forall b <- AMFX, c <- b.AMFO :: inside(b,c));

  assert ntrnl > owner >= bound; //IN-KLON    //or sgiould this have some contexts somnewhere?
  assert AMFO  > AMFX  >= AMFB;   //IN-KLON

// just can't be done here!!!
// assert OwnersValid();
// assert Ready();
// assert (forall os <- allExternalOwners() :: AMFO >= os.AMFO);


    assert fieldModes == ks;
    assert fields == map[];
    assert nick == name;

    assert CallOK(oo, context);
//HACK    assert CallOK(context);
//    CallOKAMFO(oo, context);

    assert  (this in context+{this}) by { reveal COK(), CallOK(); }
    assert  (AMFO <= context+{this}) by { reveal COK(), CallOK(); }

    assert CallOK(oo, context);
    CallOKWiderContext(oo, context,{this});
    assert CallOK(oo, context+{this});

  // assert CallOK(oo.AMFO, {this}+context) by { assert {this}+context == context+{this}; }


    assert COK(this, {this}+context) by
        {
          reveal COK();
          var thistext :=  {this}+context;
          var a := this;
          assert (a in thistext);
          assert (a.AMFB <= a.AMFO <= thistext);
          assert (forall oo <- a.AMFX :: oo.Ready());
          AMFOsisAMFOs5();
          assert (forall oo <- a.AMFX, ooo <- oo.AMFO :: a.AMFO > oo.AMFO >= ooo.AMFO);
          assert (forall oo <- a.AMFO, ooo <- oo.AMFX :: a.AMFO >= oo.AMFO > ooo.AMFO);
          assert (a.Ready());
          assert (a.Valid());
          assert (a.AllOutgoingReferencesAreOwnership(thistext));
          assert (a.AllOutgoingReferencesWithinThisHeap(thistext));

          assert (a.AllOwnersAreWithinThisHeap(thistext));
          assert AllTheseOwnersAreFlatOK(a.AMFX, thistext);

          assert COK(a, thistext);
        }


////¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢¢
//
//           assert (this in ({this}+context));
//           assert (this.AMFO <= ({this}+context));
//           RVfromCallOK(oo,context);
//
//           assert (forall x <- owner, xo <- x.AMFO :: xo in x.AMFO);
//
//
//           assert AMFO == flattenAMFOs(oo) + {this};
//           assert this !in flattenAMFOs(oo);
//           assert (forall a <- oo  :: a.Ready());     //why are these here?
//           assert (forall a <- oo  :: AMFO > a.AMFO);
//
//           // assert (forall oo  <- AMFO  :: AMFO > oo.AMFO);
//
//           assert (forall o <- (allExternalOwners()) :: o.Ready());
//           assert (forall o <- (allExternalOwners()) :: AMFO > o.AMFO);
//
//           assert AMFO == (flatten(ntrnl - {this}) + {this});
//           assert forall b <- AMFO, c <- b.AMFO :: c in AMFO && inside(b,c) && inside(this,c);
//           assert AMFX == flatten(owner);
//           assert AMFO == (flatten(owner) + {this});
//
//           assert (this.Ready());
//           assert (this.Valid());
//           assert (this.AllOutgoingReferencesAreOwnership(({this}+context)));
// // 1       assert (this.AllOutgoingReferencesWithinThisHeap(( //>>>
//           assert (this.AllOwnersAreWithinThisHeap(({this}+context)));
//
//           reveal AllTheseOwnersAreFlatOK();
//
//           assert AllTheseOwnersAreFlatOK(AMFX);
//
//           reveal COK();

          // // assume COK(a, thistext);  ///FUCKER
          // assert COK(this, {this}+context) by {
          //       assume (forall oo <- a.AMFO :: oo.Ready());
          //       assume (forall o <- (a.AMFO - {a}), ooo <- o.AMFO :: a.AMFO >= o.AMFO > ooo.AMFO);
          //       assume (a.AllOwnersAreWithinThisHeap(thistext));
          //       assume AllTheseOwnersAreFlatOK(a.AMFX);
          //       reveal COK(), AllTheseOwnersAreFlatOK();
          //       assert COK(a, thistext);
          // }






  assert COKOK: COK(this, context+{this})
    by { assert  {this}+context == context+{this}; }

  CallOKfromCOK(this, {this}+context);

  assert CallOK({this}, {this}+context);

  COKAMFO(oo, context);
assert CallOK(flattenAMFOs(oo), context);
CallOKWiderContext(flattenAMFOs(oo), context, {this});
assert context + {this}  == {this} + context;
assert CallOK(flattenAMFOs(oo),  {this} + context);

  CallOKWiderFocus({this}, flattenAMFOs(oo), {this} + context);




  assert CallOK({this} + flattenAMFOs(oo), {this} + context);

  //assert CallOK(xtra, context);

  assert  CallOK({this} + flattenAMFOs(oo), {this} + context);

  assert COK(this, context+{this}) by { reveal COKOK; }

//print "Object.make() just constructed ", fmtobj(this), "\n";

assert (forall b <- AMFX, c <- b.AMFO :: c in AMFO);
assert (forall b <- AMFX  :: b.Ready());
assert (forall b <- AMFX, c <- b.AMFO :: b.Ready());
assert (forall b <- AMFX, c <- b.AMFO :: b.Ready());
forall b <- AMFX, c <- b.AMFO  ensures (inside(b,c))
  {
    fucked(b);
    fucked(c);
    assert inside(b,c);
    assert inside(this,c);
  }
assert (forall b <- AMFX, c <- b.AMFO :: inside(this,c));


assert (forall b <- AMFX, c <- b.AMFO :: c in AMFO && inside(b,c) && inside(this,c));


assert
  && (forall oo <- AMFX :: AMFO > oo.AMFO)
  && (forall oo <- AMFX :: oo.Ready())
  && (forall x <- AMFX, oo <- x.AMFO ::  AMFO > oo.AMFO)
  && (forall b <- AMFX, c <- b.AMFO :: c in AMFO && inside(b,c) && inside(this,c))
  by {
    reveal COKOK;
    reveal COK(), CallOK();
  }


assert forall o <- owner, ooo <- o.AMFO :: o.AMFO >= ooo.AMFO;
assert forall o <- AMFO :: AMFO >= o.AMFO;


//HACKETU HACKETY HACK - wnat to prove
///assert forall o <- AMFO,  ooo <- o.AMFO :: AMFO >= o.AMFO >= ooo.AMFO;


assert forall ooo <- this.AMFO :: AMFO >= this.AMFO >= ooo.AMFO;
assert forall oo <- (AMFO - {this}) :: (AMFO > oo.AMFO) && oo.Ready();
assert forall oo <- (AMFO - {this}), ooo <- oo.AMFO :: oo.Ready() && ooo.Ready();

assert forall oo <- (AMFO - {this}), ooo <- oo.AMFO ::
   && (oo.Ready())
   && (ooo.Ready())
   && (AMFO > oo.AMFO);


forall oo <- (AMFO - {this}), ooo <- oo.AMFO
  ensures (oo.AMFO >= ooo.AMFO)
  {
    fucked(oo);
    fucked(ooo);
  }

assert forall oo <- (AMFO - {this}),  ooo <- oo.AMFO :: AMFO >= oo.AMFO >= ooo.AMFO;

   assert OwnersValid();
   assert Ready();
  }//end make()j


lemma fucked(o : Object)
  requires o.Ready()
  ensures  forall oo <- o.AMFX :: oo.Ready()
  ensures  forall oo <- o.AMFO :: o.AMFO >= oo.AMFO
  ensures  forall oo <- o.AMFO, ooo <- oo.AMFO :: ooo.Ready()
  ensures  forall oo <- o.AMFO, ooo <- oo.AMFO :: oo.AMFO >= ooo.AMFO
  {}


  constructor fake(ks : map<string,Mode>, oo : Owner, context : set<Object>, name : string, mb : Owner := oo)
  {
    owner := oo;
    bound := mb;
    AMFO := flattenAMFOs(oo) + {this};
    fieldModes := ks;
    fields := map[];
    nick := name;
    new;

   // print "Object.fake() just constructed ", fmtobj(this), "\n";
  }














lemma triceratops(aa : set<Object>, bb : set<Object>, cc : set<Object>)
  ensures (aa + bb + cc) == ((aa + bb) + cc) == (aa + (bb + cc))
{}

lemma noFieldsAreAlwaysGoodFields()
 requires fields == map[]
 ensures  AllFieldsAreDeclared()
 ensures  AllFieldsContentsConsistentWithTheirDeclaration()
{}

lemma flatOwnersConvariantOK1(xx : set<Object>, yy : set<Object>)
  requires AllTheseOwnersAreFlatOK(xx,xx+yy)
  ensures  flattenAMFOs(xx) <= yy + xx
{
  reveal AllTheseOwnersAreFlatOK();
  assert AllTheseOwnersAreFlatOK(xx,xx+yy);
}

lemma flatOwnersConvariantOK2(xx : set<Object>, yy : set<Object>)
  ensures AllTheseOwnersAreFlatOK(xx,xx+yy) == ( flattenAMFOs(xx) <= yy + xx )
{
  reveal AllTheseOwnersAreFlatOK();
  assert AllTheseOwnersAreFlatOK(xx,xx+yy) == ( flattenAMFOs(xx) <= yy + xx );
}

lemma anoyingExternalOwners()
  requires Ready()
  ensures (forall os <- allExternalOwners() :: AMFO >= os.AMFO)
{}




predicate Ready()
  // invariants on static features of this - notably between the variosu owner / AMFO fields
  // see alsos COK, BoundNessting, BoubndsNetingFrom and AMFOsisAMFOs5
   reads {}
   decreases AMFO, 20
  {
    && (AMFB == flatten(bound))
    && (AMFX == flatten(owner))
    && (AMFO == (flatten(ntrnl - {this}) + {this}))
    && (AMFO == (flatten(owner) + {this}))
    && (AMFO == AMFX + {this})
    && (AMFX == AMFO - {this})

//from older OwnersValid()
  && (owner >= bound)
  && (forall b <- AMFO, c <- b.AMFO :: c in AMFO && inside(b,c) && inside(this,c))
//end older OwnersValid()

    && (this !in AMFB)
    && (this !in AMFX)
    && (this  in AMFO)

    && ntrnl > owner >= bound  //IN-KLON    //or sgiould this have some contexts somnewhere?
    && AMFO  > AMFX  >= AMFB   //IN-KLON

    && (forall oo <- owner :: AMFO > oo.AMFO)
    && (forall oo <- bound :: AMFO > oo.AMFO)
    && (forall oo <- owner :: oo.Ready())
    && (forall oo <- bound :: oo.Ready())
    && (forall oo <- AMFX  :: AMFO > oo.AMFO)
    && (forall oo <- AMFX  :: oo.Ready())

    && (forall oo <- owner :: (AMFO > oo.AMFO) && oo.Ready())
    && (forall oo <- (AMFO - {this}) :: (AMFO > oo.AMFO) && oo.Ready())

    && (forall oo <- AMFO :: AMFO >= oo.AMFO)
    && (forall o <- owner, ooo <- o.AMFO :: AMFO >  o.AMFO >= ooo.AMFO)
    && (forall o <- AMFO,  ooo <- o.AMFO :: AMFO >= o.AMFO >= ooo.AMFO)

  }

lemma u(o : Object)
  requires o.Ready()
  ensures  o !in o.AMFB
  ensures  o !in o.AMFX
  ensures  o  in o.AMFO
{}



function allExternalOwners() : (rv : set<Object>)
 //all o's owners except o itself
  // decreases AMFO, 30
   { AMFX }

function allExternalBounds() : set<Object>
 //all o's
 {  AMFB  } //AMFB can't have "this" in it...


lemma allExternalOwnersIncludesBounds()
  requires Ready()
  ensures  allExternalOwners() >= allExternalBounds()
{}

lemma allExternalOwnersIncludesKlown(m : Klon)
  requires Ready()
  requires allExternalOwners() <= m.m.Keys
    ensures  m.ownersInKlown(this)
{
  assert m.m.Keys >= AMFX >= AMFB;

}

///*opaque*/
predicate Valid()
  decreases |AMFO|
//  reads ValidReadSet()`fields,  ValidReadSet()`fieldModes
   reads this`fields, this`fieldModes
     requires Ready()
  //ensures Valid() ==> g()
 // reads this, this`Owner, AMFO, fields.Values, AMFO`fields, AMFO`Owner,
 //    (set o1 <- AMFO, o2 <- o1.fields.Values :: o2) //JESUS MARY AND JOSEPH AND THE WEE DONKEY
  {
    OwnersValid()
       &&
  /////////KJX {:todo}  REINSTATE COS WITHOUT DOESNT HELP IS EVEIL EVILEVILEVIL
    AllFieldsAreDeclared()
        &&
    AllFieldsContentsConsistentWithTheirDeclaration()
    //    &&
    //  (forall o <- AMFO :: recInside(this, o))     //recInside needs valid, OOPS.
  //  //  &&
    // 3eReferencesAreVenice()
  }

  predicate AllFieldsAreDeclared()
    reads this`fields, this`fieldModes
    { fields.Keys <= fieldModes.Keys }

  predicate AllFieldsContentsConsistentWithTheirDeclaration()
    requires AllFieldsAreDeclared()
    reads this`fields, this`fieldModes
    {
      forall n <- fields :: AssignmentCompatible(this, fieldModes[n], fields[n])
    }

  predicate AllOutgoingReferencesAreOwnership(os : set<Object>)
    reads this`fields//, fields.Values,  os//semi-evil
    requires Ready() // ||  TRUMP()
    //requires forall n <- fields :: ownersOK(fields[n],os)
    {
       && (forall n <- fields :: refOK(this, fields[n]))
    }

  predicate AllOutgoingReferencesWithinThisHeap(os : set<Object>)
    reads this`fields //, fields.Values, this, os//semi-evil
    requires Ready() // || TRUMP()
    //requires forall n <- fields :: ownersOK(fields[n],os)
    {
       outgoing() <= os
    }

lemma NoFieldsAreGoodFields(context : set<Object>)
  requires fields == map[]
  requires Ready()
  ensures AllOutgoingReferencesAreOwnership(context)
  ensures AllOutgoingReferencesWithinThisHeap(context)
{
}


  predicate AllOwnersAreWithinThisHeap(os : set<Object>)
    // reads this, fields.Values, this, os//semi-evil
    requires Ready() //requires forall n <- fields :: ownersOK(fields[n],os)
    {
    //   (allExternalOwners() + allExternalBounds()) <= os
    // &&  (allExternalOwners() <= os)
    // &&  (allExternalBounds() <= os)
      && (AMFO <= os)
      && (AMFB <= os)
    }

  function outgoing() : set<Object> reads this`fields { fields.Values }
  function fieldNames() : set<string> reads this`fields { fields.Keys }    //WAS {  fieldModes.Keys }
  function size() : nat reads this`fields { |outgoing()| }


function ValidReadSet() : set<Object>
reads this`fields, AMFO`fields
 {
{this} + fields.Values + AMFO +
     (set o1 <- AMFO, o2 <- o1.fields.Values :: o2) //JESUS MARY AND JOSEPH AND THE WEE DONKEY
}

lemma ReadyGetsOwnersValid()
  requires Ready()
  ensures OwnersValid()
{
  //////reveal Ready();
reveal Ready();
assert OwnersValid();
}




predicate  OwnersValid() : (rv : bool) //newe version with Ready {}Mon18Dec2024}
  decreases AMFO, 10
  reads {}
  {
  && (AMFB == flattenAMFOs(bound))
  && (AMFX == flattenAMFOs(owner))
  && (AMFO == flattenAMFOs(owner) + {this})

  && (this !in bound)
  && (this !in owner)
  && (this !in AMFB)
  && (this !in AMFX)
  && (this  in AMFO)

  && (AMFO > AMFX >= AMFB)
  && (owner >= bound)


  && (forall o <- bound :: o.Ready())
  && (forall o <- owner :: o.Ready())


  && (forall oo <- AMFX :: AMFO > oo.AMFO)
  && (forall oo <- AMFX :: oo.Ready())
  && (forall x <- AMFX, oo <- x.AMFO ::  AMFO > oo.AMFO)
  && (forall b <- AMFX, c <- b.AMFO :: c in AMFO && inside(b,c) && inside(this,c))

//  && (AMFB == flattenAMFOs(bound) + {this}) //WTFFF - how is thatPOSSIBLE - 20Dec2024
//
  }


lemma AMFOsisAMFOs()
//my AMFO encompasses all my external owners AMFOs
   requires Ready()
   ensures  forall oo <- AMFO | oo != this :: (AMFO > oo.AMFO)
{}


lemma AMFOsisAMFOs1()
//my AMFO encompasses or equals my owners AMFOs (equals if its me)
   requires Ready()
   requires OwnersValid()
   ensures forall oo <- AMFO :: oo.AMFO <= AMFO
{}

lemma AMFOsisAMFOs2()
//my AMFO encompasses or equals my owners' owners' AMFOs (equals if its me)
   requires Ready()
   requires OwnersValid()
   ensures forall x <- AMFO, oo <- x.AMFO :: oo.AMFO <= AMFO
{}

lemma AMFOsisAMFOs3()
   // AMFX is flattern (externa) owners and works OK
   requires Ready()
   requires OwnersValid()
   ensures allExternalOwners() == flattenAMFOs(owner) == AMFX
   ensures AMFO == (AMFX + {this})
   ensures this in AMFO
   ensures allExternalOwners() ==  AMFO - {this}
   ensures this !in AMFX
{}

lemma AMFOsisAMFOs4()
   requires Ready()
   requires OwnersValid()
ensures
  && (forall oo <- owner :: AMFO > oo.AMFO)
  && (forall oo <- AMFX  :: AMFO > oo.AMFO)
  && (forall oo <- AMFO :: (oo != this) ==> (AMFO > oo.AMFO))
  && (forall o <- AMFO :: inside(this, o))  // {todo could move   this out}
  && (AMFX == AMFO - {this})
  && (AMFO >= AMFB)
{}


lemma AMFOsisAMFOs5()
   requires Ready()
   requires OwnersValid()
   ensures (forall oo <- AMFX, ooo <- oo.AMFO :: AMFO >  oo.AMFO >= ooo.AMFO)
   ensures (forall oo <- AMFX, ooo <- oo.AMFO :: AMFO >= oo.AMFO >= ooo.AMFO)
   ensures (forall oo <- AMFX, ooo <- oo.AMFX :: AMFO >  oo.AMFO >  ooo.AMFO)
   ensures (forall oo <- AMFX, ooo <- oo.AMFX :: AMFO >= oo.AMFO >= ooo.AMFO)
{
   assert  (forall oo <- AMFX :: AMFO > oo.AMFO);
   assert  (forall oo <- AMFX :: oo.Ready());
   assert  (forall oo <- AMFX, ooo <- oo.AMFO :: ooo.Ready());
   assert  (forall oo <- AMFX, ooo <- oo.AMFX :: oo.AMFO > ooo.AMFO);
   assert  (forall oo <- AMFX, ooo <- oo.AMFO :: oo.AMFO >= ooo.AMFO);
   assert  (forall oo <- AMFX, ooo <- oo.AMFX :: AMFO > oo.AMFO > ooo.AMFO);
   assert  (forall oo <- AMFO, ooo <- oo.AMFO :: AMFO >= oo.AMFO >= ooo.AMFO);
}


lemma CallMyOwnersWillWitherAway(a : Object, context : set<Object>)
     //if CallOK(context) && COK(a,context)
     //then my owners & AMFOs are all OK in context too
  requires CallOK(context)
  requires (a in context) || (COK(a, context))  //umm why the ||

  ensures  CallOK(a.owner, context)
  ensures  a.owner <= context  //should follow
  ensures  a.AMFO <= context  //ditto, etc...
  ensures  forall oo <- a.AMFO :: COK(oo, context) //ditto - no idea if it's good to keep these or not.
  ensures  CallOK(a.AMFO, context)
{
  reveal   CallOK();
  reveal   COK();
}


/*opaque*/ predicate TRUMP() ///*opaque*/ Valid()
    reads this`fields, this`fieldModes
 //  reads ValidReadSet()`fields, ValidReadSet()`fieldModes
   {
//for OvenReady()
//end OvenReady()
    Ready() && Valid()
   }

lemma BIDEN()
  requires TRUMP()
  ensures  && Ready() && Valid()
{
   //////reveal TRUMP();
}

lemma VANCE(aa : set<Object>)
  ensures forall o <- aa ::   o.TRUMP() ==> o.Ready()
{}



function deTRUMP(gop : Object) : (dem : Object)
    reads gop.ValidReadSet()`fields, gop.ValidReadSet()`fieldModes
    reads gop`fields, gop`fieldModes
    requires gop.TRUMP()
    ensures  dem.Ready()
    ensures  dem.Valid()

{  gop.BIDEN();  gop }


lemma AllStandaloneMonotonic(aa : set<Object>, bb : set<Object>)
   //we have MOGO(aa);  SUPERMOGO(bb,aa+bb); ==> MOGO(aa+bb);
///note that there's *no* constraint saying aa !! bb

  requires forall o <- (aa) :: (o.TRUMP())
  ensures  forall o <- aa ::   o.TRUMP() ==> o.Ready()
  requires forall o <- (aa) :: (deTRUMP(o).AllOutgoingReferencesAreOwnership(aa))
  requires forall o <- (aa) :: (o.Ready() && o.AllOutgoingReferencesWithinThisHeap(aa))
  requires forall o <- (aa) :: (o.Ready() && o.AllOwnersAreWithinThisHeap(aa))

  requires forall o <- (bb) :: (o.TRUMP())
  requires forall o <- (bb) :: (deTRUMP(o).AllOutgoingReferencesAreOwnership(aa+bb))
  requires forall o <- (bb) :: (o.Ready() && o.AllOutgoingReferencesWithinThisHeap(aa+bb))
  requires forall o <- (bb) :: (o.Ready() && o.AllOwnersAreWithinThisHeap(aa+bb))

  ensures  forall o <- (aa) :: (o.TRUMP())
  ensures  forall o <- (aa) :: (o.Ready() && o.AllOutgoingReferencesAreOwnership(aa+bb))
  ensures  forall o <- (aa) :: (o.Ready() && o.AllOutgoingReferencesWithinThisHeap(aa+bb))
  ensures  forall o <- (aa) :: (o.Ready() && o.AllOwnersAreWithinThisHeap(aa+bb))
{
}



/*opaque*/ predicate MOGO() : (rv : bool)
   reads set o1 <- (AMFO + {this}), o2 <- o1.ValidReadSet() :: o2`fields
   reads (AMFO + {this})`fields
   reads set o1 <- (AMFO + {this}), o2 <- o1.fields.Values :: o2`fields
   reads set o1 <- (AMFO + {this}), o2 <- o1.ValidReadSet() :: o2`fieldModes
   reads (AMFO + {this})`fieldModes
   reads set o1 <- (AMFO + {this}), o2 <- o1.fields.Values :: o2`fieldModes
  //  reads set o1 <- (AMFO + {this}), o2 <- o1.ValidReadSet() :: o2
  //  reads (AMFO + {this}), (AMFO + {this})`fields
  //  reads set o1 <- (AMFO + {this}), o2 <- o1.fields.Values :: o2
  // ensures SUPERMAGA( {this} + AMFO, {this} + AMFO)   ///be nice, but I wannt make verythiug TRUMP?
{
  //////reveal MOGO();
  MAGA({this} + AMFO)
}

//all aa's individually MAGA-ishg within context
//MAGA could be rewritteninterhsmof this?
/*opaque*/ predicate SUPERMAGA(aa : set<Object>, context : set<Object>)
   reads  set o1 <- (aa+context), o2 <- o1.ValidReadSet() :: o2
   reads (aa+context), (aa+context)`fields
   reads set o1 <- (aa+context), o2 <- o1.fields.Values :: o2
   requires forall o <- (aa) :: o.TRUMP()
   requires forall o <- (context) :: o.TRUMP()
{
  && (forall o <- (aa) :: (deTRUMP(o).Ready()))
  && (forall o <- (aa) :: (o.AllOutgoingReferencesAreOwnership(context))  )
  && (forall o <- (aa) :: (o.AllOutgoingReferencesWithinThisHeap(context)))
  && (forall o <- (aa) :: (o.AllOwnersAreWithinThisHeap(context)))
}



/*opaque*/ predicate MAGA(aa : set<Object>) : (rv : bool)
  //  reads (set o1 <- aa, o2 <- o1.ValidReadSet() :: o2)
  //  reads  set o1 <- aa, o2 <- o1.ValidReadSet() :: o2
  //  reads aa, aa`fields
  //  reads set o1 <- aa, o2 <- o1.fields.Values :: o2
   reads (set o1 <- aa, o2 <- o1.ValidReadSet() :: o2)`fields
   reads (set o1 <- aa, o2 <- o1.ValidReadSet() :: o2)`fieldModes
   reads aa`fields, aa`fieldModes
   reads set o1 <- aa, o2 <- o1.fields.Values :: o2`fields
   reads set o1 <- aa, o2 <- o1.fields.Values :: o2`fieldModes
  // ensures rv ==> SUPERMAGA(aa,aa)
{
  var res :=
  && (forall o <- (aa) :: (o.TRUMP()))
  && (forall o <- (aa) :: (deTRUMP(o).AllOutgoingReferencesAreOwnership(aa))  )
  && (forall o <- (aa) :: (o.AllOutgoingReferencesWithinThisHeap(aa)))
  && (forall o <- (aa) :: (o.AllOwnersAreWithinThisHeap(aa)));
assert true;
  res
}



} //end class Object


//compare the fucking AllOwnersAreWthinThisHeap???
//why in here, not in Ownerhsip.dfy?
//why opaqie all of a sudden?
// thisi  kind of SHITTY.
// given one arg, yes they are all flat,
// given TWO args, checks all owners flattenAMFOs witin context!!!
/*opaque*/ predicate AllTheseOwnersAreFlatOK(os : set<Object>, context : set<Object> := os)
// true iff all os's AMFOS are inside os
// probalby need to do - {a} if these are for {a} or else it gets circular...?  //INDEED
{
//  && (forall o <- os :: o in o.AMFO)
  && flattenAMFOs(os) <= context
}   //IT"S NOT CLEAR OWHAT THIS SHOULD DO (or if it matters)
    //&& flattenAMFOs(a.AMFO - {a}) <= a.AMFO  //should it be this?
    //&& flattenAMFOs(a.AMFO - {a}) <= (a.AMFO - {a}) //or should it be this instead?
    //&& flattenAMFOs(a.AMFO + {a}) <= (a.AMFO + {a}) //or even this?


lemma FlatAMFOsAreFlat(os : set<Object>, of : set<Object>, context : set<Object>)
  requires of == flattenAMFOs(os)
  requires of <= context
  ensures  AllTheseOwnersAreFlatOK(os, context)
{
  reveal AllTheseOwnersAreFlatOK();
}




predicate OrigBigfoot(os : set<Object>, context : set<Object> := os)
//os and the AMFO of every o in os are inside the context
//alternative formulation of AllTheseOwnerAreFlatOK
{
  && (os <= context)
  && (forall o <- os :: o.AMFO <=  context)
}

predicate Bigfoot(os : set<Object>, context : set<Object> := os) : ( r : bool )
    ensures r ==> AllTheseOwnersAreFlatOK(os,context)
{
  reveal AllTheseOwnersAreFlatOK();
  OrigBigfoot(os,context)
}


//extra lemma pshychoBigFoot moved to Klon.dfy

lemma SPLATTO(os : set<Object>, context : set<Object> := os)
  ensures OrigBigfoot(os,context) == AllTheseOwnersAreFlatOK(os,context)
{
  reveal AllTheseOwnersAreFlatOK();
}

lemma MaybeOrMaybeNot(o : Object, os : set<Object>)
//does it matter of we care if "this" is in the set of AMFO's we're flattening?
//I dob't think so, as long as it's OK...?
//or rather, if os are OKJ, o.AMFO <= os, os+o are OK too...
  requires o !in flattenAMFOs(os)
  requires AllTheseOwnersAreFlatOK(os)
  requires o.AMFO <= (os + {o})
  ensures  AllTheseOwnersAreFlatOK(os+{o})
  {
    reveal AllTheseOwnersAreFlatOK();
  }

/*oopaque or not or both */
function flattenAMFOs(os : set<Object>) : (of : set<Object>)
   //flattened set of os.AMFO
   //earlier version required o in all objects AMFS, that's gone now
   //could put it back, require os Ready, or remove the os+ below
   //currently going with the version with fewer requirements...
   //requires forall o <- os :: o in o.AMFO  //not needed adding
   ensures os <= of
   ensures of >= os
   ensures forall o <- os :: o.AMFO <= of
{
    os +   ///not technically needed if we keep "requires forall o <- os :: o in o.AMFO"
    (set o <- os, oo <- o.AMFO :: oo)
}


function flatten(os : Owner) : Owner {flattenAMFOs(os)}
function flattenBound(os : Owner) : Owner
   //union of flattened bounds (AMFB) of all os
   {set o <- os, oo <- o.AMFB :: oo}

lemma AMFOisBigger(o : Object)
  requires o.Ready()
  ensures  (forall oo <- o.allExternalOwners() :: o.AMFO > oo.AMFO)
  ensures  (forall oo <- o.AMFX                :: o.AMFO > oo.AMFO)
 {
   assert o.AMFO == flattenAMFOs(o.owner) + {o};
   assert o.AMFO == flattenAMFOs(o.owner + {o});

   assert (forall oo <- o.allExternalOwners() :: o.AMFO > oo.AMFO);
 }

//GRRRR
// lemma EitherWayIsFlat(a : Object, rrm : Map, amx : set<Object>)
//   //requires rrm.calid()
//   requires forall o <- a.extra, oo <- o.AMFO ::
//           && o in rrm.m.Keys
//           && oo in rrm.m.Keys
//           && rrm.m[o]  in amx
//           && rrm.m[oo] in amx
//   ensures  AllTheseOwnersAreFlatOK(a.extra, amx)
// {
//   assert flattenAMFOs(mapThruMap(a.extra,rrm)) <= amx;
// }




lemma Splurge(o : Object, context : set<Object>)
  requires COK(o, context)

  ensures  forall oo <- (o.AMFO - {o}) :: o.AMFO > oo.AMFO
  ensures  reveal COK(); flattenAMFOs(o.AMFO - {o}) <= o.AMFO
  ensures  AllTheseOwnersAreFlatOK(o.allExternalOwners())
{
  reveal COK();
  assert COK(o, context);
  RVfromCOK(o, context);
  assert o.Ready();

  assert o in o.AMFO;
  assert forall oo <- (o.AMFO - {o}) :: oo.Ready();
  assert forall oo <- (o.AMFO - {o}) :: oo in oo.AMFO;
  assert forall oo <- (o.AMFO - {o}) :: o !in oo.AMFO;
  assert forall oo <- (o.AMFO - {o}) :: o.AMFO > oo.AMFO;

 assert flattenAMFOs(o.AMFO) <= o.AMFO;
}



  predicate  {:vcs_split_on_every_assert}{:timeLimit 10} StandaloneObjectsAreValid(os : set<Object>) //do we know if "os" is "closed"?
    // reads set o <- os, rd <- ({o} + o.fields.Values) :: rd
  //  requires OutgoingReferencesAreInTheseObjects(os)   ///why is this needed now?

    //requires os <= objects
    //reads this, objects
    requires forall o <- os :: o.Ready() && o.Valid()
    reads os,  os`fields//, os`Owner //os`AMFO,
    reads (set o1 <- os, o2 <- o1.ValidReadSet() :: o2)

    // //reads set o <- os :: o`AMFO
    // reads set o <- os :: o
    // reads set o <- os :: o`fields

    // reads (set o1 <- os, o2 <- o1.ValidReadSet() :: o2)

    //reads objects`fields, objects`Owner // objects`AMFO,
    {
     forall o <- os :: StandaloneObjectIsValid(o,os)
    }


// todo: rename with a "withinthisheap" or something?
predicate {:todo "really todo - add in other cases"}  StandaloneObjectIsValid(o : Object, os : set<Object>)
   reads o`fields, o`fieldModes
   reads os`fields, os`fieldModes
  //  reads os, o, o.ValidReadSet()
  //  reads (set o1 <- os, o2 <- o1.ValidReadSet() :: o2)
   requires o.Ready()
   requires forall o <- os :: o.Ready() && o.Valid()
    {
       && (o.Valid())
       && (o.AllOutgoingReferencesAreOwnership(os))
//       && (o.AllOutgoingReferencesWithinThisHeap(os))
//       && (o.AllOwnersAreWithinThisHeap(os))
    }




predicate OutgoingReferencesAreInTheseObjects(os : set<Object>)
      reads os
      //note that this is within *this objectset
      //see also OutgoingReferencesAreInThisHeap
{
     (forall o <- os :: o.outgoing() <= os)
}

predicate OutgoingHeapReferencesAreInTheseObjects(os : set<Object>)
      reads os
{
//      (forall f <- os, t <- f.outgoing() :: t in os )
      (forall f <- os :: f.outgoing() <= os )

}

predicate OutgoingReferencesFromTheseObjectsAreToTheseObjects(fs : set<Object>, ts : set<Object>)
      reads fs
{
     (forall f <- fs :: f.outgoing() <= ts)
}

predicate OutgoingHeapReferencesFromTheseObjectsAreToTheseObjects(fs : set<Object>, ts : set<Object>)
      reads fs
{
//     (forall f <- fs, t <- f.outgoing() :: t in ts )
     (forall f <- fs :: f.outgoing() <= ts)
}




lemma NoIncomingReferencesMeansNoOutgoingReferences(o : Object, os : set<Object>)
   requires forall o <- os :: o.Ready() && o.Valid()  ///grrr..
   requires incomingEdges(o, edges(os)) == {}
   requires OutgoingReferencesFromTheseObjectsAreToTheseObjects(os, os+{o})///HMM
   ensures  forall e <- edges(os) :: e.t != o
   ensures  forall x <- os :: (outgoingEdges(x, edges(os)) <= edges(os))
   ensures  forall x <- os, e <- outgoingEdges(x, edges(os)) :: e.t != o
   ensures  forall x <- os :: o !in x.outgoing()
   ensures  OutgoingReferencesAreInTheseObjects(os)
   {
     var es := edges(os);
     var ie := incomingEdges(o, edges(os));
     assert ie == {};
     assert (set e <- es | e.t == o) == {};


    //attempt at contradiction
    if (exists e <- es :: e.t == o)
    {
      var e :|  e in es && e.t == o;
      assert e in es;
      assert e in ie;
      assert ie != {};
      assert false;
    }
    assert not(exists e <- es :: e.t == o);
    assert forall e <- es :: e.t != o;

    edgesWork(os,es);
    edgesWorks2(os,es);
    assert ObjectsToEdges(os,es);

    assert forall x <- os :: o !in x.outgoing();

   }






lemma RefCountDistributesOverDisjointEdges(oo : set<Object>, aa : set<Edge>, bb : set<Edge>)
      requires aa !! bb
      ensures
       forall i <- oo ::
         refCountEdges(i, aa + bb) == refCountEdges(i, aa) + refCountEdges(i, bb)
       ensures
       forall i <- oo ::
         incomingEdges(i, aa + bb) == incomingEdges(i, aa) + incomingEdges(i, bb)
    {
      //calc == {
       assert forall i <- oo ::
            (set e <- aa | e.t == i) + (set e <- bb | e.t == i)
            == (set e <- (aa+bb) | e.t == i);
       assert forall i <- oo ::
            incomingEdges(i,aa) + incomingEdges(i,bb)
            == incomingEdges(i,aa+bb);
       assert forall i <- oo ::
            refCountEdges(i,aa) + refCountEdges(i,bb)
            == refCountEdges(i,aa+bb);
      //}
    }




lemma ClosedHeapContainsAllFieldValues(os : set<Object>)
  requires OutgoingReferencesAreInTheseObjects(os)
  ensures allFieldValues(os) <= os
  {}



//xs old objectset
//f n t - assignment.
//f.n not in xs
twostate lemma edgeFUCKINGassignment(os : set<Object>,
      rs : set<Edge>, rn : set<Edge>,
                            f : Object, n : string, t : Object)
  //reads f`fieldModes
  requires forall o <- os :: o.Ready() && o.Valid()
  requires f in os
  requires n !in old(f.fields)
///for OvenReady() for some reason
  requires n in old(f.fieldModes)
///end OvenReady() for some reason
  requires t in os
  requires rs == old(edges(os))
  requires rn ==     edges(os)
  //permits f == t or f != t
  requires forall o <- os ::
           forall m <- old(o.fields) ::
             m in o.fields && o.fields[m] == old( o.fields[m] )
  requires forall o <- os :: unchanged(o`fieldModes)
          //  forall m <- old(o.fieldModes) ::
          //    m in o.fieldModes && o.fieldModes[m] == old( o.fieldModes[m] )
  requires forall o <- (os) ::
           forall m <- (o.fields) ::
             ( (m in old(o.fields) && o.fields[m] == old( o.fields[m] ))
                 || (o == f && m == n &&  o.fields[m] == t)
             )
  requires n in f.fields
  requires f.fields[n] == t

  ensures  n in f.fields
  ensures  f.fields[n] == t
  ensures  edges(os) == old(edges(os)) + {Edge(f,n,f.fieldModes[n],t)}
        {}





lemma HeyFUCKOFF(x : Object, y : Object, zz : set<Object>)
  requires x in zz+{y}
  requires x != y
  ensures  x in zz
{}



//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
/// auxiliary stuff...
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

function allFieldValues(os : set<Object>) : set<Object>
  reads os
{
set o <- os, v <- o.fields.Values :: v
}

twostate lemma allFieldValuesUnchangedObject(o : Object)
  requires unchanged(old(o.fields.Values))
  ensures unchanged(old(allFieldValues({o})))
{}

twostate lemma allFieldValuesUnchanged(os : set<Object>)
  requires forall o <- os :: unchanged(old(o.fields.Values))
  ensures unchanged(old(allFieldValues(os)))
{
 forall o <- os { allFieldValuesUnchangedObject(o); }
}

function allFieldValuesExcept(os : set<Object>, xo : Object) : set<Object>
  reads os
{
set o <- os, v <- o.fields.Values | o != xo :: v
}




 lemma FEWERFIELDS(a : Object)
   requires a.Ready()
   ensures  mapLEQ(a.fields, old(a.fields))
   ensures  a.Ready()
{}

lemma ALLFEWERFIELDS(os : set<Object>)
   requires forall a <- os :: a.Ready()
   ensures  forall a <- os :: mapLEQ(a.fields, old(a.fields))
   ensures  forall a <- os :: a.Ready()
{}



//
// derived lemmas equality etc
//

lemma AXIOMAMFOS(a : Object, b : Object)
// equal AMFOs iff same objects
  requires a.Ready()
  requires b.Ready()
  ensures  (a == b)  ==> (a.AMFO == b.AMFO)
  ensures  (a == b) <==  (a.AMFO == b.AMFO)
  ensures  (a == b) <==> (a.AMFO == b.AMFO)
{}


lemma AXIOMAMFO(part : Object, whole : Object)
// o in AMFO ==> o.AMFO <= AMFO
   requires  part.Ready()
   requires  {whole}    <= part.AMFO
   ensures   whole.AMFO <= part.AMFO
   ensures   inside(part,whole)
   {
    part.AMFOsisAMFOs();
   }

lemma AXIOMAMFOREVERSE(part : Object, whole : Object)
// inside(part,whole) ==> whole in part.AMFO
   requires   part.Ready()
   requires   whole.Ready()
   requires   part.AMFO >= whole.AMFO

   requires   inside(part,whole)
   ensures    whole in part.AMFO
   {
    assert whole in whole.AMFO;
    part.AMFOsisAMFOs();
   }