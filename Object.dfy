
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
    case Rep | Owned(_) | Loaned(_) => inside(v,o) //KJX is this right  hmm?
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
//
class Object { 
  var nick : string //nickname
  const owner : Owner//actual "dynamic" Owner owner of this object
     //it's changed to a var now so lots of comoplaints.
     //fuck should I change it back?  or not? - no point in bheing VAR while AMFO is CONST!
  var   fields     : map<string,Object>//field values. uninit fields have no entries
  var   fieldModes : map<string,Mode>//Mode of each field name -  note, static! - would be statically known by any methods
    //probably also has to go to var to get to typestate. GRRR. 

  const AMFO : Owner //All MY FUCKING Owner  (aka All My Flat Owner:-)

 
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



  constructor make(ks : map<string,Mode>, oo : Owner, context : set<Object>, name : string) 
    requires forall o <- oo :: o.Ready()
    requires CallOK(oo, context)
    requires CallOK(context) //KJX is this redundant Or wouidl it be redundat the other way around???
    // requires AllTheseOwnersAreFlatOK(oo)  //hmm? what would this mean?
    //requires CallOK({oo}+oo.AMFO, context)

    //KJX shouldn't there be some topological restriction on where or when
    //you can create new objects/contexts / regions?
    //what sgoiuld they be?

    requires CallOK(flattenAMFOs(oo), context) //KJX is this right?

    ensures owner == oo 
    ensures fieldModes == ks
    ensures fields == map[] 
    ensures AMFO == flattenAMFOs(oo) + {this}
    ensures this  in AMFO
    ensures this !in owner

    ensures (forall oo <- allExternalOwners() :: AMFO >= oo.AMFO)
    ensures (forall o <-  AMFO :: inside(this, o))

    ensures OwnersValid()
    ensures Ready()

                                                                                   
    ensures COK(this, context+{this})                  
    ensures nick == name
  
    //ensures CallOK({this} + {oo}+oo.AMFO, {this} + context)

    ensures unchanged( context )
    ensures fresh(this)

  { 
    owner := oo;
    fieldModes := ks;
    fields := map[];
    AMFO := flattenAMFOs(oo) + {this};
    nick := name;
    new;   


    assert fieldModes == ks;
    assert fields == map[];
    assert nick == name;

    assert CallOK(oo, context);
    assert CallOK(context);
    CallOKAMFO(oo, context);
    assert  (this in context+{this}) by { reveal COK(), CallOK(); } 
    assert  (AMFO <= context+{this}) by { reveal COK(), CallOK(); } 

    assert CallOK(oo, context);
    CallOKWiderContext(oo, context,{this});
    assert CallOK(oo, context+{this});

  // assert CallOK(oo.AMFO, {this}+context) by { assert {this}+context == context+{this}; }
  

    assert COK(this, {this}+context) by 
        { 
          reveal COK();
  
          assert (this in ({this}+context));
          assert (this.AMFO <= ({this}+context));
          RVfromCallOK(oo,context);

           
          
  

          assert (forall x <- owner, xo <- x.AMFO :: xo in x.AMFO);
  

          assert AMFO == flattenAMFOs(oo) + {this}; 
          assert this !in flattenAMFOs(oo);
          assert (forall a <- oo  :: a.Ready());     //why are these here?
          assert (forall a <- oo  :: AMFO > a.AMFO); 
  
          // assert (forall oo  <- AMFO  :: AMFO > oo.AMFO); 

          assert (forall o <- (allExternalOwners()) :: o.Ready());
          assert (forall o <- (allExternalOwners()) :: AMFO > o.AMFO);
          assert (this.Ready());
          assert (this.Valid()); 
          assert (this.AllOutgoingReferencesAreOwnership(({this}+context)))  ;
          assert (this.AllOutgoingReferencesWithinThisHeap(({this}+context)));
          assert (this.AllOwnersAreWithinThisHeap(({this}+context)));

          reveal AllTheseOwnersAreFlatOK();

          assert AllTheseOwnersAreFlatOK(allExternalOwners());

          assert COK(this, {this}+context);
         }




  assert COKOK: COK(this, context+{this}) 
    by { assert  {this}+context == context+{this}; }

  CallOKfromCOK(this, {this}+context);
 
  assert CallOK({this}, {this}+context);

assert CallOK(flattenAMFOs(oo), context);
CallOKWiderContext(flattenAMFOs(oo), context, {this});
assert context + {this}  == {this} + context;
assert CallOK(flattenAMFOs(oo),  {this} + context);

  CallOKWiderFocus({this}, flattenAMFOs(oo), {this} + context);


assert (forall oo <- allExternalOwners() :: AMFO >= oo.AMFO);      

  assert CallOK({this} + flattenAMFOs(oo), {this} + context);

  //assert CallOK(xtra, context);

  assert  CallOK({this} + flattenAMFOs(oo), {this} + context);

  assert COK(this, context+{this}) by { reveal COKOK; }

//print "Object.make() just constructed ", fmtobj(this), "\n";
  }























/*opaque*/ predicate Ready() 
// ready means all the owenrs are (at least) ready...
// I had to inline the defition --- see "//Ready()inlined"
// WHO the fuck knows WHY?
// update this, update that too.

//it's important: this has *no*  readsclausew
   decreases AMFO, 1  
{
  && (AMFO == (flattenAMFOs(owner) + {this}))
  && (allExternalOwners() == flattenAMFOs(owner))  //KJX hmmm again 
  && (AMFO == (allExternalOwners() + {this}))      //KJX hmmm indeed
  && (forall oo <- owner :: AMFO > oo.AMFO)
  && (forall oo <- owner :: oo.Ready())
  // && (flattenAMFOs(allExternalOwners()) <= AMFO)
  //KJX hmmma
  && OwnersValid()
  }



function allExternalOwners() : set<Object>
 //all o's owners except o itself
 {  AMFO - {this} }

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
       allExternalOwners() <= os
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


//KJX should refactor all these invariants
predicate OwnersValid() : (rv : bool) //newe version with Ready {}Mon18Dec}
  decreases AMFO, 0
  //requires Ready()
  {  
  && (this  in AMFO)
  && (this !in owner)
  && (owner <= AMFO)
  && (AMFO == flattenAMFOs(owner) + {this})
  && (forall o <- AMFO :: inside(this, o))  // {todo could move   this out}
  && (forall b <- AMFO, c <- b.AMFO :: c in AMFO && inside(b,c) && inside(this,c))
  }


lemma AMFOsisAMFOs() 
   requires Ready()
   requires OwnersValid()
   ensures forall oo <- AMFO :: oo.AMFO <= AMFO
{}

lemma AMFOsisAMFOs2() 
   requires Ready()
   requires OwnersValid()
   ensures forall x <- AMFO, oo <- x.AMFO :: oo.AMFO <= AMFO
{}


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
   { Ready() && Valid() }

lemma BIDEN() 
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
// given TWO args, checks all owners flatten witin context!!!
opaque predicate AllTheseOwnersAreFlatOK(os : set<Object>, context : set<Object> := os)
// true iff all os's AMFOS are inside os
// probalby need to do - {a} if these are for {a} or else it gets circular...?  //INDEED
{
//  && (forall o <- os :: o in o.AMFO)
  && flattenAMFOs(os) <= context
}   //IT"S NOT CLEAR OWHAT THIS SHOULD DO (or if it matters)
    //&& flattenAMFOs(a.AMFO - {a}) <= a.AMFO  //should it be this?
    //&& flattenAMFOs(a.AMFO - {a}) <= (a.AMFO - {a}) //or should it be this instead?
    //&& flattenAMFOs(a.AMFO + {a}) <= (a.AMFO + {a}) //or even this?

predicate OrigBigfoot(os : set<Object>, context : set<Object> := os) 
//os and the AMFO of every o in os are bound by context
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
   //could put it back, require os to be Ready, or remove the os+ below
   //currently going with the version with fewer requirements...
   //requires forall o <- os :: o in o.AMFO  //not needed adding
{
    os +   ///not technically needed if we keep "requires forall o <- os :: o in o.AMFO"
    (set o <- os, oo <- o.AMFO :: oo)
}

lemma AMFOisBigger(o : Object)
  requires o.Ready()
  ensures  (forall oo <- o.allExternalOwners() :: o.AMFO >= oo.AMFO)
 {
   assert o.AMFO == flattenAMFOs(o.owner) + {o};
   assert o.AMFO == flattenAMFOs(o.owner + {o});

   assert (forall oo <- o.allExternalOwners() :: o.AMFO >= oo.AMFO);
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

  // assert o in o.AMFO;
//  assert forall oo <- (o.AMFO - {o}) :: oo in oo.AMFO;
  // assert forall oo <- (o.AMFO - {o}) :: o !in oo.AMFO;
  // assert forall oo <- (o.AMFO - {o}) :: o.AMFO > oo.AMFO;

//  assert flattenAMFOs(o.AMFO) <= o.AMFO;
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


















