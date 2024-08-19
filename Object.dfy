
datatype Region = World                         // region of immutable objects
                  | Heap(owner : Object)         // objects allocated in heap region


datatype Mode =   
    | Rep // owned by me
    | Peer // owned by my owner
//For all the Owner & Read "Modes" sholdn't the owner always be "self" i.e; the object containing the reernce.
    | Owned(perm : Perm) //unrestricted, Rust-style owning reference - with no borrows!
    | Loaned(perm : Perm) //owning reference, but currently there are "borrowed" references to it
    | Borrow(perm: Perm, owner: Region, from : Object, name : string) //borrowed reference, borrowe from that object!
                                      //when one does a "stack-pop-return" into the obejct that this was borrowed from
                                      //then the Mode of the owning refernece goes from Loaned -> Owned 
    | Evil //type dyanmic.  So I don't hace to do the full checks right now --- kjx 7 May 2024


datatype Perm = Read | Write | Local   ///or should these be object kinds???>  ARGH!!


    /// an earlier deprecated design!
    // | Own(perm : Region) //unrestricted, Rust-style owning reference?
    // | Read(owner : Region) //Rust stule ownering Readonly reference? 
    //                        //IF we have move semantics, could move here from Own?
    // | ReadOwn(owner : Region)  // I am the owner, but my contents are read-borrowed.
    // | MutOwn(owner : Region)  // I am the owner, but my contents are mut-borrowed.
    // | LocOwn(owner : Region)  // I am the owner, but my contents are loc-borrowed.
    // | ReadRef(owner : Region) //       

predicate AssignmentCompatible(o : Object, t : Mode, v : Object) 
//can object v be assigned to a field of Mode t within object o?
{
  match t  
    case Evil => true
    case Rep | Owned(_) | Loaned(_) => v.region.Heap? && v.region.owner == o
    case Peer => v.region == o.region
//  case Borrow(p,b,n,f) => v.region == b
    case Borrow(p,b,n,f) => refOK(o,v)
}


lemma EVILisCompatibleWithAnything(o : Object, v : Object)
  ensures AssignmentCompatible(o, Evil, v)
{}




























//////////////////////////////////////////////////////////////////////////////
//  OBJECTS
//
//I know it's perverse, but titlecase "Object" and "Class" aren't reserved in dafny
//
//note that null / undefined fields can be declared in objects
//but may not necessarily be in the Object's fields.

class Object { 
  var nick : string //nickname
  const region : Region//actual "dynamic" region owner of this object
     //it's changed to a var now so lots of comoplaints.
     //fuck should I change it back?  or not? - no point in bheing VAR while AMFO is CONST!
  var   fields     : map<string,Object>//field values. uninit fields have no entries
  var   fieldModes : map<string,Mode>//Mode of each field name -  note, static! - would be statically known by any methods
    //probably also has to go to var to get to typestate. GRRR. 

  const AMFO : set<Object> //All MY FUCKING Owners  (aka All My Flat Owners:-)

  const extra : set<Object> //additional owners e.g. for stack frames inside objects

lemma {:onlyNUKE} triceratops(aa : set<Object>, bb : set<Object>, cc : set<Object>) 
  ensures (aa + bb + cc) == ((aa + bb) + cc) == (aa + (bb + cc))
{}



lemma {:onlyNUKE} cordelia() 
 requires fields == map[]
 ensures  AllFieldsAreDeclared()
 ensures  AllFieldsContentsConsistentWithTheirDeclaration()
{}






//:onlyGRUNTS} 
  constructor {:isolate_assertions} cake(ks : map<string,Mode>, oo : Object, context : set<Object>, name : string, xtra : set<Object> := {} ) 
    requires COK(oo, context)
    requires CallOK(context)
    requires CallOK(xtra, context) 
    requires ExtraIsExtra(xtra, context)
    //requires CallOK({oo}+oo.AMFO, context)

    requires xtra == {} //extra not yet cloned


    ensures region == Heap(oo)
    ensures fieldModes == ks
    ensures fields == map[] 
    ensures extra == xtra
    ensures AMFO == oo.AMFO + {this} + xtra
    ensures this in AMFO
    ensures this !in extra
    ensures nick == name
    ensures (forall o <- AMFO :: inside(this, o))
    
    ensures COK(this, context+{this})
    //ensures CallOK({this} + {oo}+oo.AMFO, {this} + context)

    ensures unchanged( context )
    modifies {}
  { 
    region := Heap(oo);
    fieldModes := ks;
    fields := map[];
    AMFO := oo.AMFO + xtra + {this};
    nick := name;
    extra := xtra;
    new;   

    assert fieldModes == ks;
    assert fields == map[];
    assert nick == name;
    assert extra == xtra;

    assert COK(oo, context);
    assert CallOK(context);
    COKAMFO(oo, context);
    assert  (this in context+{this}) by { reveal COK(), CallOK(); } 
    assert  (xtra <= context) by { reveal COK(), CallOK(); } 
    assert  (AMFO <= context+{this}) by { reveal COK(), CallOK(); } 
    assert CallOK(oo.AMFO, context); 
    assert (oo.AMFO) <= context by { reveal CallOK(), COK(); }
    CallOKWiderContext(oo.AMFO,context,{this});
    assert CallOK(oo.AMFO, {this}+context) by { assert {this}+context == context+{this}; }


    assert COK(this, {this}+context) by 
        { 
          reveal COK();
  
          assert (this in ({this}+context));
          assert (this.AMFO <= ({this}+context));
          RVfromCOK(oo,context);
          assert (forall a <- oo.AMFO  :: a.Ready()); 
          assert (forall a <- oo.AMFO  :: AMFO > a.AMFO); 

          RVfromCallOK(extra, context);
          assert (forall a <- extra    :: a.Ready()); 

          assert AMFO == oo.AMFO + extra + {this};
          assert this !in oo.AMFO;
          assert this !in extra;

          assert CallOK(extra,context);
          assert AMFO == oo.AMFO + {this} + xtra;
          assert ExtraIsExtra(extra,context);
          assert (forall x <- extra :: x in x.AMFO);
          assert (forall x <- extra, xo <- x.AMFO :: xo in x.AMFO);
          assert (forall x <- {region.owner}, xo <- x.AMFO :: xo in x.AMFO);
  

          assert region.owner.Ready();
          assert (forall owner <- (AMFO - {this}) :: owner.Ready());
          assert (forall owner <- (AMFO - {this}) :: AMFO > owner.AMFO);
          assert (this.Ready());
          assert (this.Valid());    
          assert (this.AllOutgoingReferencesAreOwnership(({this}+context)))  ;
          assert (this.AllOutgoingReferencesWithinThisHeap(({this}+context)));
          assert (this.AllOwnersAreWithinThisHeap(({this}+context)));
         }




  assert COKOK: COK(this, context+{this}) 
    by { assert  {this}+context == context+{this}; }

  CallOKfromCOK(this, {this}+context);
 
  assert CallOK({this}, {this}+context) ;

  CallOKWiderFocus({this}, oo.AMFO, {this} + context);

  assert CallOK({this} + (oo.AMFO), {this} + context);

  //assert CallOK(xtra, context);

  assert  CallOK({this} + oo.AMFO, {this} + context);

  assert COK(this, context+{this}) by { reveal COKOK; }

  }




















  constructor {:onlyFROZZ} frozen(ks : map<string,Mode>) 
    ensures region == World
    ensures fieldModes == ks
    ensures fields == map[] //object fields starts uninitialised
    ensures AMFO == {this}
    ensures this in AMFO
    ensures this !in extra
    ensures Ready()
    ensures OwnersValid()
    ensures Valid()
    ensures TRUMP()
    ensures nick is string
    ensures MOGO()
    ensures  fresh(this)    
    ensures extra == {}
    modifies {}
  { //////reveal Ready(); //////reveal TRUMP(); //////reveal MAGA(); //////reveal MOGO();
    region := World;
    fieldModes := ks;
    fields := map[];
    AMFO := {this};
    nick := "";
    extra := {};
    new;
    assert extra == {};
    assert Ready();
    assert AMFO <= AMFO;
    assert AllOwnersAreWithinThisHeap(AMFO);
    assert fields == map[];
    assert AllOutgoingReferencesAreOwnership(AMFO);
    assert AllOutgoingReferencesWithinThisHeap(AMFO);
    assert OwnersValid();
    assert Valid();
    assert TRUMP();
    assert MOGO();
  }

constructor {:onlyFROZZ} frozen2(ks : map<string,Mode>, oHeap : set <Object>) 
    ensures region == World
    ensures fieldModes == ks
    ensures fields == map[] //object fields starts uninitialised
    ensures AMFO == {this}
    ensures this in AMFO
    ensures this !in extra
    ensures Ready()
    ensures OwnersValid()
    ensures Valid()
    ensures TRUMP()
    ensures nick is string
    ensures MOGO()

    ensures unchanged(oHeap)
    requires CallOK(oHeap)
    ensures  CallOK(oHeap)
    ensures  COK(this,oHeap+{this})
    ensures  fresh(this)
    ensures extra == {}    
    modifies {}
  { //////reveal Ready(); //////reveal TRUMP(); //////reveal MAGA(); //////reveal MOGO();
    region := World;
    fieldModes := ks;
    fields := map[];
    AMFO := {this};
    nick := "";
    extra := {};
    new;
    assert extra == {};    assert Ready();
    assert fields == map[];
    assert OwnersValid();
    assert Valid();
    assert TRUMP();
    assert MOGO();
  
    var context := (oHeap+{this});
    assert this in context;
    assert AMFO <= context;
    assert forall oo <- AMFO :: oo.Ready();
    assert (Ready() && Valid());
    assert AllOutgoingReferencesAreOwnership(context);
    assert AllOutgoingReferencesWithinThisHeap(context);
    assert AllOwnersAreWithinThisHeap(context);
    reveal COK();
    assert COK(this,context);
  }







/*opaque*/ predicate {:onlyNUKE} Ready() 
// ready means all the owenrs are (at least) ready...
// I had to inline the defition --- see "//Ready()inlined"
// WHO the fuck knows WHY?
// update this, update that too.

//it's important: this has *no*  readsclausew
   decreases AMFO
{
  && (this !in extra)
  && (region.World? || region.Heap?)
  && (region.World? ==> (AMFO == {this}))
  && (region.World? ==> (extra == {}))
  && (region.Heap?  ==> (AMFO == region.owner.AMFO + extra + {this}))
  && (region.Heap?  ==> (AMFO > region.owner.AMFO))
  && (region.Heap?  ==> region.owner.Ready())
  && (region.Heap?  ==> (forall owner <- region.owner.AMFO :: AMFO > owner.AMFO))
  && (region.Heap?  ==> (forall owner <- region.owner.AMFO :: owner.Ready()))
  && (forall owner <- (AMFO - {this}) :: AMFO > owner.AMFO)
  && (forall owner <- (AMFO - {this}) :: owner.Ready())
  && (forall owner <- (extra)         :: AMFO > owner.AMFO)   //subsumed by the above 2 lines, but...
  && (forall owner <- (extra)         :: owner.Ready())
  }



function owners() : set<Object>
 //all o's owners except o itself
 {  AMFO - {this} }

///*opaque*/ 
predicate {:onlyValid} Valid()
  decreases |AMFO|
//  reads ValidReadSet()`fields,  ValidReadSet()`fieldModes
   reads this`fields, this`fieldModes
     requires Ready()
  //ensures Valid() ==> OwnersValid()
 // reads this, this`region, AMFO, fields.Values, AMFO`fields, AMFO`region, 
 //    (set o1 <- AMFO, o2 <- o1.fields.Values :: o2) //JESUS MARY AND JOSEPH AND THE WEE DONKEY
  {
    (region.World? || region.Heap?)   //turn off other regions  //HMMM
        &&
    OwnersValid()
       &&
  /////////KJX {:todo}  REINSTATE COS WITHOUT DOESNT HELP IS EVEIL EVILEVILEVIL
    AllFieldsAreDeclared()
        &&
    AllFieldsContentsConsistentWithTheirDeclaration()
    //    &&
    //  (forall o <- AMFO :: recInside(this, o))     //recInside needs valid, OOPS.
  //  //  && 
    // AllOutgoingReferencesAreVenice()
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
       owners() <= os
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
assert OwnersValid(); 
}



predicate {:onlyNUKE} OwnersValid() : (rv : bool) //newe version with Ready {}Mon18Dec}
  decreases AMFO
  //requires Ready()
  {  
  && (Ready())
  && (region.World? || region.Heap?)  
  && (this in AMFO)
  && (region.World? ==> (AMFO == {this}))
  && (region.Heap? ==> (AMFO > {}))
  && ((region.Heap?) ==> region.owner in AMFO)
  && ((region.Heap?) ==> assert region.owner in AMFO; AMFO > region.owner.AMFO)
  && ((region.Heap?) ==> (AMFO == region.owner.AMFO + extra + {this}))
  && ((region.Heap?) ==> assert region.owner in AMFO; region.owner.Ready())
  && (forall own <- (AMFO - {this}) :: (own.AMFO < AMFO) && own.Ready())
  && (forall o <- AMFO :: inside(this, o))  // {todo could move   this out}
  && (forall b <- AMFO, c <- b.AMFO :: c in AMFO && inside(b,c) && inside(this,c))
  }



// predicate  {:vcs_split_on_every_assert}  WTFOwnersValid() : (rv : bool) //newe version with Ready {}Mon18Dec}
//   decreases AMFO
//   ensures rv ==> (region.World? || region.Heap?)  
//   ensures rv ==>  (this !in AMFO)
//   ensures rv ==>  (region.World? ==> (AMFO == {}))
//   ensures rv ==>  (region.Heap? ==> (AMFO > {}))
//   ensures rv ==>  ((region.Heap?) ==> region.owner in AMFO)
//   ensures rv ==>  ((region.Heap?) ==> assert region.owner in AMFO; AMFO > region.owner.AMFO)
// //  ensures rv ==>  ((region.Heap?) ==> assert region.owner in AMFO; |AMFO| > |region.owner.AMFO|)
//   ensures rv ==>  ((region.Heap?) ==> (AMFO == region.owner.AMFO + {region.owner}))
//   ensures rv ==>  ((region.Heap?) ==> assert region.owner in AMFO; region.owner.Ready())
//   ensures rv ==>  (forall own <- (AMFO - {this}) :: (own.AMFO < AMFO) && own.Ready())
//   ensures rv ==>  (forall o <- AMFO :: inside(this, o))  // {todo could move   this out}
//   ensures rv ==>  (forall b <- AMFO, c <- b.AMFO :: c in AMFO && inside(b,c) && inside(this,c))
//     //  ensures (forall b <- AMFO, c <- b.AMFO :: c in AMFO && recInside(b,c) && recInside(this,c)))
//   {  
//      //////reveal Ready();
//      Ready() 
//   }


lemma {:onlyAMFO} AMFOsisAMFOs() 
   requires Ready()
   requires OwnersValid()
   ensures forall oo <- AMFO :: oo.AMFO <= AMFO
{}

lemma {:onlyAMFO} AMFOsisAMFOs2() 
   requires Ready()
   requires OwnersValid()
   ensures forall x <- AMFO, oo <- x.AMFO :: oo.AMFO <= AMFO
{}


lemma  CallMyOwnersWillWitherAway(a : Object, context : set<Object>)
  requires CallOK(context)
  requires (a in context) || (COK(a, context))
  ensures  a.AMFO <= context
  ensures  forall oo <- a.AMFO :: COK(oo, context)
  ensures a.region.Heap? ==> COK(a.region.owner,context)
  ensures a.region.Heap? ==> a.region.owner in context
{
  reveal   CallOK();
  reveal   COK();
}


/*opaque*/ predicate {:onlyTRUMP} TRUMP() ///*opaque*/ Valid() 
    reads this`fields, this`fieldModes
 //  reads ValidReadSet()`fields, ValidReadSet()`fieldModes
   { Ready() && Valid() }

lemma {:onlyTRUMP} BIDEN() 
  requires TRUMP()
  ensures Ready() && Valid()
{
   //////reveal TRUMP();
}

function deTRUMP(gop : Object) : (dem : Object)
    reads gop.ValidReadSet()`fields, gop.ValidReadSet()`fieldModes
    requires gop.TRUMP()
    ensures  dem.Ready()
    ensures  dem.Valid()

{  gop.BIDEN();  gop }


lemma AllStandaloneMonotonic(aa : set<Object>, bb : set<Object>)
   //we have MOGO(aa);  SUPERMOGO(bb,aa+bb); ==> MOGO(aa+bb);
///note that there's *no* constraint saying aa !! bb

  requires forall o <- (aa) :: (o.TRUMP())  
  requires forall o <- (aa) :: (deTRUMP(o).AllOutgoingReferencesAreOwnership(aa))  
  requires forall o <- (aa) :: (o.AllOutgoingReferencesWithinThisHeap(aa))
  requires forall o <- (aa) :: (o.AllOwnersAreWithinThisHeap(aa))

  requires forall o <- (bb) :: (o.TRUMP())  
  requires forall o <- (bb) :: (deTRUMP(o).AllOutgoingReferencesAreOwnership(aa+bb))  
  requires forall o <- (bb) :: (o.AllOutgoingReferencesWithinThisHeap(aa+bb))
  requires forall o <- (bb) :: (o.AllOwnersAreWithinThisHeap(aa+bb))

  ensures  forall o <- (aa) :: (o.TRUMP())  
  ensures  forall o <- (aa) :: (o.AllOutgoingReferencesAreOwnership(aa+bb))  
  ensures  forall o <- (aa) :: (o.AllOutgoingReferencesWithinThisHeap(aa+bb))
  ensures  forall o <- (aa) :: (o.AllOwnersAreWithinThisHeap(aa+bb))
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
/*opaque*/ predicate {:onlyWANKER} SUPERMAGA(aa : set<Object>, context : set<Object>)
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

//extended validity




predicate  ExtraIsExtra(xtra : set<Object>, context : set<Object>)
  // why did I put all thjese READS clases im hjere - when they are unnecessary..?
  // reads (set x <- xtra, xa <- x.AMFO :: xa)`fields
  // reads (set x <- xtra, xa <- x.AMFO :: xa)`fieldModes
  // reads  xtra`fields, xtra`fieldModes
{
//  && CallOK(xtra, context) ///DO I WANT THIS, O JUST "READY"""
  && (forall e <- xtra :: e in e.AMFO)
  && (forall e <- xtra :: e.AMFO <= (xtra))
  && (forall e <- xtra :: e.AMFO <= context)
  //&& (forall e <- xtra :: e.AMFO <= xtra)     //is this want we want..?
}


/*oopaque or not or both */
function flattenAMFOs(os : set<Object>) : (of : set<Object>)
   requires forall o <- os :: o in o.AMFO
   ensures  forall o <- os :: o in of
   ensures  forall o <- os, oo <- o.AMFO :: oo in of
   ensures  os <= of
{
    os + 
    (set o <- os, oo <- o.AMFO :: oo)
}


lemma FlatExtras(xtra : set<Object>, context : set<Object>)
   requires forall o <- xtra :: o in o.AMFO
   requires forall o <- xtra :: o.AMFO <= context
   requires CallOK(xtra, context)
   ensures  CallOK(xtra, context)
   ensures (forall e <- xtra :: e.AMFO <= context)
   ensures  xtra <= context 
  // ensures  ExtraIsExtra(flattenAMFOs(xtra), context)
   {
     reveal CallOK(), COK();
     assert CallOK(xtra, context);// by { reveal fuka;}
     assert ExtraIsExtra(flattenAMFOs(xtra), context);  
  
   }


  predicate  {:vcs_split_on_every_assert}{:timeLimit 10} StandaloneObjectsAreValid(os : set<Object>) //do we know if "os" is "closed"?
    // reads set o <- os, rd <- ({o} + o.fields.Values) :: rd
  //  requires OutgoingReferencesAreInTheseObjects(os)   ///why is this needed now?
  
    //requires os <= objects   
    //reads this, objects
    requires forall o <- os :: o.Ready() && o.Valid()
    reads os,  os`fields//, os`region //os`AMFO,
    reads (set o1 <- os, o2 <- o1.ValidReadSet() :: o2)

    // //reads set o <- os :: o`AMFO
    // reads set o <- os :: o
    // reads set o <- os :: o`fields

    // reads (set o1 <- os, o2 <- o1.ValidReadSet() :: o2)

    //reads objects`fields, objects`region // objects`AMFO,
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
  // OutgoingReferencesAreInTheseObjects(os)
      (forall f <- os, t <- f.outgoing()
         | f.region.Heap? && t.region.Heap? :: t in os ) 
}

predicate OutgoingReferencesFromTheseObjectsAreToTheseObjects(fs : set<Object>, ts : set<Object>) 
      reads fs
{
     (forall f <- fs :: f.outgoing() <= ts) 
}

predicate   OutgoingHeapReferencesFromTheseObjectsAreToTheseObjects(fs : set<Object>, ts : set<Object>) 
      reads fs
{
//  OutgoingReferencesFromTheseObjectsAreToTheseObjects(fs,ts)
     (forall f <- fs, t <- f.outgoing()
      | f.region.Heap? && t.region.Heap? :: t in ts ) 
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
  ensures edges(os) == old(edges(os)) + {Edge(f,n,f.fieldModes[n],t)}
        {}





lemma {:onlyONLY} HeyFUCKOFF(x : Object, y : Object, zz : set<Object>)
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


















