//Clone_Via_Map -> Clone_Clone_Clone ✅
//Clone_Clone_Clone -> Clone_All_Owners, Object.make(), putInside/putOutside, Clone_All_Fields
//Clone_All_Owners -> Clone_Via_Map✅
//Clone_All_Fields -> Clone_Field_Map
//Clone_Field_Map ->  Clone_Via_Map

method Clone_Via_Map(a : Object, m' : Klon)
  returns (b : Object, m : Klon)
  //entry point for Clone - clones a according to map m'
  //begin with m' empty
  decreases |m'.oHeap - m'.m.Keys|, |a.AMFO|, |a.fields.Keys|, 20 //Klone_Via_Map

  requires m'.calid()
  requires m'.readyAll()
  requires allMapOwnersThruKlownOK(m')
  // requires a in m'.oHeap  //technically redundant given COKx
  requires COK(a, m'.oHeap) //ties owners into OHEAP but not KLON MAP
  requires m'.readyOK(a)

  requires klonCanKV(m',a,a)

  ensures  m.calid()

  ensures  a in m.m.Keys
  ensures  m.m[a] == b
//  ensures  COK(b,m.oHeap+m.ns) ///shojuld beaable to get this

  //should I package this up - as aw twostate or a onestate?
  ensures  mapLEQ(m'.m,m.m)
//   ensures  m.m.Keys >= m'.m.Keys + {a}
//   ensures  m.m.Values >= m'.m.Values + {b}
//   ensures  m.from(m')

//   ensures  m.o == m'.o
//   ensures  m.oHeap == m'.oHeap
//   ensures  m.ns >= m'.ns

  //  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)

  ensures  klonVMapOK(m.m)
  ensures  a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
  // should we say something about b.AMFO?  b.AMFO <= m.m.Values? por again m.hasV(b)?
  // m.key(a)?  m.val(a)???
  // should decided whether to do this with AMFOs or owners
  // and don one one...
  //OK os THIS requires us to make sure all the owners are in (even if outsidef - where does that happen?)
//  ensures  m.from(m')
  //ensures b.AMFO == mapThruKlon(a.AMFO, m) //hmmm - bit it's NOT there

  // ensures  a !in m'.m.Keys ==> b !in m'.ns  //KJX sure about this?
  ensures  unchanged(a)
  ensures  unchanged(m'.oHeap)
  ensures  unchanged(m'.ns)

  ensures klonOwnersAreCompatible(a, b, m)
  ensures m.readyAll()

  ensures b.fieldModes == a.fieldModes

  ensures m.from(m')

//TOHERE

  //  ensures  fresh(b)
  //modifies m'[a]
  //  modifies m'.ns`fields //argh. pity so wide
  //modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  // modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  modifies {} // just modifes objecst allocated after this point?
{
  m := m';



print "CALL Clone_Via_Map ", fmtobj(a), " m':", fmtklon(m'), "\n";

  print "VARIANT CVM ", |(m'.oHeap - m'.m.Keys)  - {a}|, " ", |a.AMFO|, " ", |(a.fields.Keys )|, " ", 20, "\n";


  if (a in m.m.Keys){ //already cloned, return
    b := m.m[a];
    assert (
        && (klonOwnersAreCompatible(a, b, m))
        && (klonVMapOK(m.m)))
     by {
      assert m.calid();
      reveal m.calid();
      assert m.calidMap();
      reveal m.calidMap();
      assert klonAllOwnersAreCompatible(m,m.m.Keys);
      assert klonOwnersAreCompatible(a, b, m);
      assert klonVMapOK(m.m);
    }

    print "RETN Clone_Via_Map already cloned ", fmtobj(a), "\n";
    return;
  }

  if (outside(a,m.o)) { //outside. so just map to itself
    b := a;
    assert m.readyAll();
    assert klonCanKV(m,a,a);
    assert allMapOwnersThruKlownOK(m);

    assert m.AreWeNotMen(a, klonKV(m,a,a));

    assert m.calid();
    reveal m.calid();
    assert m.calidObjects();
    reveal m.calidObjects();
    assert m.m.Keys <= m.oHeap;

    assert m.calidMap();
    reveal m.calidMap();
    assert klonVMapOK(m.m);
    assert a.allExternalOwners() <= m.m.Keys;

    assert outside(a,m.o);
    assert forall oo <- a.owner :: outside(oo,m.o);   //FUCK??

    m := m.putOutside(a);
    klonSameOwnersAreCompatible(a,a,m);
    assert klonOwnersAreCompatible(a, a, m);

    assert m.readyAll() by {
      assert COK(a, m'.oHeap);
      reveal COK();
      assert m'.readyOK(a);
      assert m.m.Keys == m'.m.Keys + {a};
      assert m'.readyAll();
      KlonKVRestoresReadyAll(a,a,m',m);
      assert m.readyAll();
    }

    print "RETN Clone_Via_Map: outside ", fmtobj(a), "\n";
    return; // end outside case
  }
  else
  {
    //start of the Inside case
      b, m := Clone_Clone_Clone(a, m);
    //end of inside case
  }
  ///////////////////////////////////////////////////////////////
  //tidying up after the cases..

  // assert a !in m'.m.Keys ==> b !in m'.ns;   //KJX sure about this?

  reveal m.calid();
  assert m.calid();
  reveal m.calidObjects();
  assert m.calidObjects();
  reveal m.calidOK();
  assert m.calidOK();
  assert CallOK(m.m.Values, m.oHeap+m.ns);
  assert b in m.m.Values;
  assert b in m.m.Values;
  COKfromCallOK(b, m.m.Values, m.oHeap+m.ns);
  assert COK(b, m.oHeap+m.ns);
  assert BOK: COK(b, m.oHeap+m.ns);
  //  assert fresh(b);   //umm, yeah should probalboy be fresh at least if INSIDE, but...
  //  have to experiment with a clause somewhere in calidSheep saying every inside clone is new
  //  or everyhing in ns2 is new. or...
  //   assert b in m.ns;

  assert m.m[a] == b;
  assert a !in m'.m.Keys;
  // assert b !in m'.oHeap;   //need to decided whet)her this is (nominally) both iunsier or outside, or just inside
  //assert b !in m'.ns;;


  //  assert  b.fields.Keys == {};

  assert  b.fieldModes.Keys == a.fieldModes.Keys;

  reveal m.calidSheep();
  assert m.calidSheep();

  assert  b.fieldModes == a.fieldModes;

  //  assert a !in m'.m.Keys ==> b !in m'.ns;   //KJX sure about this?

  //  assert m.from(m') by {
  //      reveal m.from();
  assert  m.o     == m'.o;
  assert  m.oHeap == m'.oHeap;
  assert  m.ns    >= m'.ns;

  assert COK(b, m.oHeap+m.ns) by { reveal BOK; }

  assert m.from(m');
  //  }
  print "RETN Clone_Via_Map: ", fmtobj(a), " pivot:", fmtobj(m.o), "\n";

  assert m.readyAll();
  return;
}//END Clone_Via_Map










method Clone_Clone_Clone(a : Object, m' : Klon)
  returns (b : Object, m : Klon)
  //actually does the clone....
  // was the old Clone_Inside_Heap
    decreases |m'.oHeap - m'.m.Keys - {a}|, |a.AMFO|, |a.fields.Keys|, 15

  //this case
  requires inside(a,m'.o)
  requires a !in m'.m.Keys

  //all Clone
  requires m'.calid()
  requires a in m'.oHeap
  requires COK(a, m'.oHeap)
  //requires COK(a, m'.m.Keys+{a}) //KJXFUCKEDFRIDAY13TH

  ensures  m.calid()
  ensures  a in m.m.Keys
  ensures  b in m.m.Values
    ensures  a in m.m.Keys && m.at(a) == b
//  ensures  b in m.ns
//  ensures  COK(b, m.oHeap+m.ns)

  //should I package this up - as aw twostate or a onestate?
  //it;s about clonbamps, so clonmapLEQ or clonmapEXTENDS
  ensures  mapLEQ(m'.m,m.m)
  ensures  m.m.Keys >= m'.m.Keys + {a}
  ensures  m.m.Values >= m'.m.Values + {b}
  ensures  m.o == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns >= m'.ns
  //  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
  //  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert
  ensures klonVMapOK(m.m)
  ensures a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
//  ensures b.AMFO <= m.m.Values //do we want COK B here too? ///TUESDAY17DEC2024
  ensures b.AMFO <= m.oHeap+m.ns //TUESDAY17DEC2024
  ensures old(m'.calid())
  ensures m.from(m')

  ensures klonOwnersAreCompatible(a, b, m)

//
//   //ensures b.AMFO == set x <- a.AMFO :: m.m[x]
//
  ensures b.fieldModes == a.fieldModes
//   //   ensures b.fields.Keys == a.fields.Keys

  //modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  //modifies (set o : Object)`fields
  // ensures a !in m'.m.Keys ==> b !in m'.ns  //KJX sure about this?   //Cline INsinside heap
  // ensures b in m'.ns ==> a in m'.m.Keys
  modifies {}
{ //clone inside heap
  m := m';

m'.boundsNestingFromCalid(a, m'.oHeap);
assert COK(a, m'.oHeap);
COKWiderContext(a, m'.oHeap, m'.ns );
assert klonOwnersAreCompatible(a, a, m');

//b := a; return;///FUKOF  //16s!!!

  //FUKOF
  assert m.calid();
  assert MPRIMECALID: m.calid();
  assert inside(a,m.o);
  assert COK(a, m.oHeap);
//  assert COK(a, m.m.Keys+{a} );
//  assert AKKK: COK(a, m.m.Keys+{a} );


  print "CALL Clone_Clone_CLone of:", fmtobj(a), " owned by ", fmtown(a.owner) ,"\n";
  print "VARIANT CCC ", |(m'.oHeap - m'.m.Keys - {a})|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";

  assert CallOK(a.owner, m.oHeap) by {
    // assert COK(a, m.oHeap);
    m.calidOKFromCalid();
    // assert CallOK(m.oHeap);
    COKowner(a, m.oHeap);
    // assert CallOK(a.owner, m.oHeap);
  }

//     reveal m.calid();
//     assert m.calid();
//     reveal m.calidOK();
//     reveal m.calidOK();
//     assert CallOK(m.oHeap);
//
//     COKAMFO(a, m.oHeap);
//     assert CallOK(a.AMFO, m.oHeap);
//     assert (a.AMFO <= m.oHeap);
//
//     COKfromCallOK(a, m.oHeap);
//     assert COK(a, m.oHeap);
//     reveal COK();
//     assert a.Ready();
//     assert a.owner <= a.AMFO;
//     assert CallOK(a.owner, m.oHeap);
//
//
//     assert COK(m.o, m.oHeap);
//     assert CallOK(m.oHeap);
//     COKAMFO(a, m.oHeap);
//     assert CallOK(a.AMFO, m.oHeap);
//     assert a.owner <= a.AMFO;
//     CallOKNarrowFocus(a.owner, m.oHeap);
//     assert CallOK(a.owner, m.oHeap);
//
//   }

  //makde COK check for this, no need to do another level here?
  //... or do we - I don't (now) see why...
  // assert forall x <- a.extra :: COK(x,m.oHeap);
  // forall x <- a.extra ensures COK(x,m.oHeap)
  // {
  //   assert true;
  // }
  //assert CallOK(a.extra,m.oHeap);

assert AllTheseOwnersAreFlatOK(a.allExternalOwners()) by {
    assert COK(a, m.oHeap);
    RVfromCOK(a, m.oHeap);
    assert a.Ready();
    m.calidOKFromCalid();
    assert CallOK(m.oHeap);
    COKowner(a, m.oHeap);
    assert (a.AMFB <= a.AMFO <= m.oHeap);
    assert a.AllOwnersAreWithinThisHeap(m.oHeap);
    reveal AllTheseOwnersAreFlatOK();
    assert AllTheseOwnersAreFlatOK(a.allExternalOwners());
  }

//   assert (flattenAMFOs(a.owner) < a.AMFO) by {
//     assert m.calid();
//     reveal m.calid();
//     assert m.calidOK();
//     reveal m.calidOK();
//     COKfromCallOK(a, m.oHeap);
//     assert COK(a, m.oHeap);
//     reveal COK();
//     assert a.Ready();
//     assert a.AMFO > flattenAMFOs(a.owner);
//     assert flattenAMFOs(a.owner) <=  a.AMFO;
//   }
//
// assert AllTheseOwnersAreFlatOK(a.owner, a.AMFO)
//   by { reveal AllTheseOwnersAreFlatOK(); }
//

//b := a; return;///FUKOF  //16s


assert m.m.Keys <= m.oHeap by {
  reveal MPRIMECALID;
  assert m.calid();
  reveal m.calid();
  assert m.calidObjects();
  reveal m.calidObjects();
  assert m.m.Keys <= m.oHeap;
}

  //extraOK        reveal COK(); assert a.owner.extra == {}; //extra not yet cloned

assert ((m'.oHeap - m'.m.Keys),10 decreases to (m.oHeap - m.m.Keys),5);

  assert ((m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 15
    decreases to
      (m.oHeap - m.m.Keys), a.AMFO, (a.fields.Keys), 12);

  print "Clone_Clone_Clone ", fmtobj(a), " calling CAO", fmtown(a.owner) ,"\n";
  printmapping(m.m);


/////////////////////////////////////////////////////////////////////////////////
  var rm := Clone_All_Owners(a, m);
/////////////////////////////////////////////////////////////////////////////////

//note that BOUNDS are subtypes of OWNERS BOWIE  KJXBOUNDS

  assert rm.from(m);
  assert rm.calid();
  assert a.owner <= rm.m.Keys;
  assert AOLTK: a.owner <= rm.m.Keys;
  assert a.allExternalOwners() <= rm.m.Keys;
  assert mapThruKlon(a.allExternalOwners(),rm) <= rm.m.Values;

RVfromCOK(a, rm.oHeap);
AMFUCKED(a);
  assert a.AMFO == flattenAMFOs(a.owner) + {a} by { reveal COK(); }
  assert mapThruKlon(a.AMFO - {a}, rm) <= rm.m.Values;
  assert a in a.AMFO;
  assert flattenAMFOs(a.owner) == a.AMFO - {a};

  assert rm.m.Values >= m.m.Values;

  assert rm.oHeap == m.oHeap;
  rm.boundsNestingFromCalid(a,rm.oHeap);

assert a.allExternalOwners() >= a.allExternalBounds();

  rm.calidOKFromCalid();
  assert COK(a, rm.oHeap);
     {  assert AOK: COK(a, rm.oHeap); }
//assert COK(a, rm.m.Keys+{a} ) by { reveal COK(), AKKK; }
//assert AKK: COK(a, rm.m.Keys+{a} );
  assert CallOK(rm.oHeap);
  COKowner(a, rm.oHeap);
  assert a.AMFO == flattenAMFOs(a.owner) + {a} by { reveal COK(); }
  //assert flattenAMFOs(a.owner) == a.allExternalOwners();
  assert a.AMFO == a.allExternalOwners() + {a} by { reveal COK(); }
  assert a.allExternalOwners() == a.AMFO - {a} by
     { reveal COK(); assert COK(a, rm.oHeap); assert a.Ready(); assert a.OwnersValid();
       assert (a.AMFO == (a.allExternalOwners() + {a})) by { reveal COK(); }
       LemmaSetXsPlusSeperateSingleton(a.allExternalOwners(), a, a.AMFO);
       assert a.allExternalOwners() == a.AMFO - {a};
          }
  assert a !in a.owner;
  //assert a !in flattenAMFOs(a.owner);
  assert a.Ready() by { assert rm.calid(); rm.calidOKFromCalid(); assert COK(a, rm.oHeap); reveal COK(); }
  assert a.allExternalOwners() == flattenAMFOs(a.owner);

//  assert mapThruKlon(a.allExternalOwners() , rm) == mapThruKlon(flattenAMFOs(a.owner), rm);

//KJXFRI20DEC2024
  // var rowner := mapThruKlon(a.owner, rm); //needs to go!
  // var rbound := mapThruKlon(a.bound, rm); //DITTO...

assert COK(a, rm.oHeap);

 var rowner := a.owner;
 var rbound := a.bound;
//KJXFRI20DEC2024
assert CallOK(rowner, rm.oHeap);
CallOKWiderContext(rowner, rm.oHeap, rm.ns);
CallOKNarrowFocus(rbound, rowner, rm.oHeap+rm.ns);


// var BAXO := mapThruKlon(a.allExternalOwners(),rm);
//
// assert BAXOK: BAXO == mapThruKlon(flattenAMFOs(a.owner), rm) <= rm.m.Values;


//assert BAXO == flattenAMFOs(mapThruKlon(a.owner, rm));

  // var rAMXO  := mapThruKlon(a.allExternalOwners(),  rm); //why this, why not a.AMFO?  --- cos b hasn't been created yet!
  // var rAMXB  := mapThruKlon(a.allExternalBounds(),  rm);   //grr...



  var rAMXO := flattenAMFOs(rowner);
  var rAMXB := flattenAMFOs(rbound);

assert rAMXO >= rAMXB;
assert ownerInsideOwner(rAMXO,rAMXB);

  // assert ROWNER_RM: rowner == mapThruKlon(a.owner, rm);

  assert rm.calid();
  assert a.owner <= rm.m.Keys;
  assert a.allExternalOwners() <= rm.m.Keys;
  assert a.allExternalOwners() == flattenAMFOs(a.owner);


  OwnersValidFromCalid(a,rm);

  assert a.bound <= rm.m.Keys;
  assert a.allExternalBounds() <= rm.m.Keys;

  assert a.allExternalBounds() == flattenAMFOs(a.bound);
  assert AllTheseOwnersAreFlatOK(a.allExternalBounds()) by
    { reveal AllTheseOwnersAreFlatOK();
      assert AllTheseOwnersAreFlatOK(a.allExternalBounds()); }
//  mapThruKlonPreservesFlatness3(a.owner, a.allExternalOwners(), rowner, rAMXO, rm);
//  mapThruKlonPreservesFlatness3(a.bound, a.allExternalBounds(), rbound, rAMXB, rm);

//b := a; return;///FUKOF  //20s





    //better name woiuld be: all All_Owners_Are_Keys or sometghung
//AMFOsFromOwnersFromCalid(a, rm);
    // except we //assuage this is true or the above call wouldn't work...?



//  mapThruKlonPreservesAMFO(a.owner, rowner, rm);
 assert CallOK(rowner, rm.oHeap+rm.ns);
//  mapThruKlonPreservesAMFO(a.bound, rbound, rm);
 assert CallOK(rbound, rm.oHeap+rm.ns);

//  mapThruKlonPreservesAMFO(a.allExternalOwners(), rAMXO, rm);
//  mapThruKlonPreservesAMFO(a.allExternalBounds(), rAMXB, rm);


assert AllTheseOwnersAreFlatOK(a.allExternalOwners());
/// mapThruKlonPreservesFlatness2(a.allExternalOwners(), rAMXO, rm);
FlatAMFOsAreFlat(rowner,rAMXO,rAMXO);
assert AllTheseOwnersAreFlatOK(rowner,rAMXO);


//KJX - I find this unimpressive
  reveal rm.calid();
  reveal rm.calidObjects();
  reveal rm.calidOK();
  reveal rm.calidMap();
  reveal rm.calidSheep();
  assert rm.calid();
  assert rm.calidObjects();
  assert rm.calidOK();
  assert rm.calidMap();
  assert rm.calidSheep();

    rm.calidOKFromCalid();

//   assert CallOK(a.owner, rm.oHeap);
//   assert CallOK(rm.oHeap);
//   assert CallOK(rm.m.Keys, rm.oHeap);
//   assert CallOK(rm.m.Values, rm.oHeap+rm.ns);
//   assert CallOK(rm.ns, rm.oHeap+rm.ns);

//KJX what the shit is going on here.
//where am I going now?
//
//   //should we rename oHeap as context?
//   //KJX why do we care about this?
//   assert COK(rm.o, rm.oHeap);
//   assert CallOK(rm.oHeap);
//
//
//   // COKAMFO(rowner, rm.oHeap+rm.ns);
//   // assert {rowner}+rowner.AMFO == rowner.AMFO+{rowner};
//   // assert CallOK({rowner}+rowner.AMFO,
//   //
//   // assert CallOK({rowner}+rowner.AMFO, rm.oHeap+rm.ns);
//
//
//   assert CallOK(rm.oHeap); //ensured by clone
//   CallOKWiderContext(rm.oHeap,rm.oHeap,rm.ns);
//   assert CallOK(rm.oHeap,rm.oHeap+rm.ns);
//
//   assert CallOK(rm.ns, rm.oHeap+rm.ns);  //ensured by clone
//   CallOKWiderFocus(rm.oHeap, rm.ns, rm.oHeap+rm.ns);
//
//   assert CallOK(rm.oHeap+rm.ns);
//
//   assert CallOK(rowner, rm.oHeap+rm.ns);  //ensured by clone
//
// ///need this for later...
//   // assert OKR0: CallOK(rowner, rm.oHeap+rm.ns);
//   // assert OKC0: CallOK(rm.oHeap+rm.ns);
// ///...or rather turns out we DONT


  if (a in rm.m.Keys) {



    m := rm;
//    b := m.at(a);
    b := m.at(a);

    assert b in rm.m.Values;
    assert CallOK(rm.m.Values, rm.oHeap+rm.ns);
    assert CallOK(rm.ns, rm.oHeap+rm.ns);
COKfromCallOK(b, rm.m.Values,rm.oHeap+rm.ns);

//
//     assert b.owner == rowner;
//     assert b.AMFO  == mapThruKlon(flattenAMFOs(a.owner), rm) + {b};

//FUCKOFF commente out becauyse FUCKOFF
//     assert m.calid();
//     assert CallOK(m.m.Values, m.oHeap+m.ns);
//     assert b in m.m.Values;
//     assert m.m.Values == m.m.Values;
//     assert b in m.m.Values;
//     assert (b in m.ns) by
//     {
//       reveal m.calid();
//       assert m.calid() && m.calidObjects() && m.calidOK() && m.calidSheep();
//       reveal m.calidSheep();
//       reveal m.AreWeNotMen();
//       assert forall x <- m.m.Keys :: m.AreWeNotMen(x, m);
//       assert b == m.m[a];
//       assert a in m.m.Keys;
//       assert inside(a,m.o);
//       assert m.m[a] in m.ns;
//       assert b in m.ns;
//     }
//     assert b in m.ns;
//     assert b in rm.ns;
//
//     COKfromCallOK(b, m.m.Values, m.oHeap+m.ns);
//     assert COK(b, m.oHeap+m.ns+{b});
//     assert COK(b, rm.oHeap+rm.ns+{b});
//
//     assert b.fieldModes == a.fieldModes;
//     assert m.calidSheep();
//
//     assert m.m.Keys >= m'.m.Keys + {a};


// assert BAXO == mapThruKlon(flattenAMFOs(a.owner), rm) <= rm.m.Values
//  by { reveal BAXOK; }

//but of course we don't know that BNAXO is actuall rm.m.AMFO
///although it is! --- for now

assert rm.calid();
//assert COK(b, m.m.Values);  //KJXTUESDAY17DEC

assert COK(b, rm.oHeap+rm.ns);

TargetOwnersReallyAreOK(b, rm);

//     assert b in m.m.Values;
//     assert b.AMFO == BAXO + {b};
//     assert b.AMFO <= m.m.Values;
//
//     assert m.m.Values >= m'.m.Values + {b};


//END FUCKOFF
    print "RETN Clone_Clone_CLone ", fmtobj(a), " already cloned: abandoning ship!!\n";
    return;
  } // a in rm.m.Keys - i.e. randomly done while cloning owners



//b := a; return;///FUKOF  //19s with just return if a cloned h7 clone_owner
//b := a; return;///FUKOF  //20s+ with full code if a cloned h7 clone_owner

  print "Clone_Clone_CLone ", fmtobj(a), " have rowner ", fmtown(rowner) ," self not yet cloned\n";
//
//   assert a !in rm.m.Keys;
//   assert a.owner <= rm.m.Keys;
//
//   assert CallOK(rowner, rm.oHeap+rm.ns);
//   assert CallOK(rm.oHeap+rm.ns);
//   CallOKNarrowFocus({},rm.oHeap+rm.ns);    //WTF is this doiung?  why?
//   assert CallOK({},rm.oHeap+rm.ns);        //and this one?
//
//
// ///need this for later...
//   assert OKR1: CallOK(rowner, rm.oHeap+rm.ns);
//   assert OKC1: CallOK(rm.oHeap+rm.ns);

//
//   var rrm := Clone_All_Owners(a, rm);
//   assert rrm.from(rm);
//
//   assert CallOK(rrm.oHeap);
//   assert CallOK(rrm.oHeap, rrm.oHeap);
//   assert CallOK(rrm.ns, rrm.oHeap+rrm.ns);
//   CallOKWiderContext(rrm.oHeap, rrm.oHeap, rrm.ns);
//   CallOKWiderFocus(rrm.oHeap, rrm.ns, rrm.oHeap+rrm.ns);
//   assert OKC2: CallOK(rrm.oHeap+rrm.ns);
//
// ///need this for later...
//
//   //COKWiderContext2(rowner, )
//
//   CallOKWiderContext2(rowner, rm.oHeap+rm.ns, rrm.oHeap+rrm.ns);
//   assert OKR2: CallOK(rowner, rrm.oHeap+rrm.ns);
//
//
//   assert a.owner <= rm.m.Keys;
//   assert a.owner <= rrm.m.Keys;
//
//   if (a in rrm.m.Keys) {
//
//     print "Clone_Clone_Clone ", fmtobj(a), "after Clone_Extra_Oners, seems a already cloned: abandoning ship!!\n";
//
//     m := rrm;
//
//     b := rrm.at(a);
//
//     assert rrm.calid();
//
//     reveal rrm.calid();
//     reveal rrm.calidObjects();
//     reveal rrm.calidOK();
//     reveal rrm.calidMap();
//     reveal rrm.calidSheep();
//     reveal rrm.AreWeNotMen();
//
//     assert rrm.calid();
//     assert rrm.calidObjects();
//     assert rrm.calidOK();
//     assert rrm.calidMap();
//     assert rrm.calidSheep();
//
//     assert inside(a, rrm.o);
//     assert (forall x <- rrm.m.Keys :: rrm.AreWeNotMen(x, rrm));
//     assert rrm.AreWeNotMen(a,rrm);
//     assert (inside(a,rrm.o)) ==> rrm.m[a] in rrm.ns;
//     assert b == rrm.m[a];
//
//     assert b in rrm.ns;
//     assert CallOK(rrm.ns, rrm.oHeap+rrm.ns);
//     COKfromCallOK(b, rrm.ns, rrm.oHeap+rrm.ns);
//     assert COK(b, rrm.oHeap+rrm.ns);
//
//     return;
//   }

var rrm := rm; //KJX THIS IS EVIL, should clean up and get rid of rrm completel6.
assert rrm.from(rm);

assert a !in rrm.m.Keys;

assert rrm.m.Keys <= rrm.oHeap;

print "Clone_Clone_Clone ", fmtobj(a), " boodle boodle boodle\n";


  reveal rrm.calid();
  reveal rrm.calidObjects();
  reveal rrm.calidOK();
  reveal rrm.calidMap();
  reveal rrm.calidSheep();

  assert rrm.calid();
  assert rrm.calidObjects();
  assert rrm.calidOK();
  assert rrm.calidMap();
  assert rrm.calidSheep();

  assert COK(a,rrm.oHeap);
//assert COK(a, rrm.m.Keys+{a} ) by { reveal AKK; }

  reveal COK();
  assert a.allExternalOwners() <= rrm.oHeap;
  assert a !in rrm.m.Keys; // by { reveal ANKS; }



//FROM HERE
//
//   assert OKR3: CallOK(rowner, rrm.oHeap+rrm.ns);
//   assert OKC3: CallOK(rrm.oHeap+rrm.ns);
//
  //preconditions for cake...
  // assert CallOK(rowner, rrm.oHeap+rrm.ns) by { reveal OKR3, OKC3; }
  // assert CallOK(rrm.oHeap+rrm.ns) by { reveal OKR3, OKC3; }
//
//
//   assert (a.AMFO - {a}) == a.allExternalOwners();
//   assert flattenAMFOs(a.AMFO - {a}) == flattenAMFOs(a.allExternalOwners());
//
//   assert a.allExternalOwners() + {a} == a.AMFO;
//   // assert flattenAMFOs(a.owner) + a.extra == (a.AMFO - {a}) == a.allExternalOwners();
//   //
//   // reveal AllTheseOwnersAreFlatOK();
//   //
//   //        assert AllTheseOwnersAreFlatOK(a.AMFO - {a}) by { reveal aFLAT; }
//   //        assert AllTheseOwnersAreFlatOK(flattenAMFOs(a.owner) + a.extra);
//   var aAMFOs := a.allExternalOwners() + {a};
//   //  assert AllTheseOwnersAreFlatOK(aAMFOs);https://www.youtube.com/
//
//
//
//   //assert forall ax <- a.extra :: imageUnderMap(ax, rrm.m[ax], rrm);
//   assert rowner == mapThruKlon(a.owner, rrm);
//   assert a.allExternalOwners() <= rrm.m.Keys;
//   //assert forall ao <- flattenAMFOs(a.owner) :: rrm.m[ao] in (rrm.m[a.owner]).AMFO;
//
//
//
//
//   // assert OrigBigfoot(flattenAMFOs(a.owner));
//   // assert AllTheseOwnersAreFlatOK(flattenAMFOs(a.owner));
//
//
//
//   //reveal AllTheseOwnersAreFlatOK();
//
//   //assert rowner.AMFO ==  mapThruKlon(flattenAMFOs(a.owner), rrm);
//   //        assert AllTheseOwnersAreFlatOK(flattenAMFOs(a.owner) + a.extra);
//   //
//   //        assert AllTheseOwnersAreFlatOK(rowner.AMFO);
//   //
//   //        assert AllTheseOwnersAreFlatOK(a.extra, a.allExternalOwners());
//
//
//   //
//   //       assert (set o <- a.extra ::  rrm.m[o]) == mapThruKlon(a.extra, rrm);
//   //       assert (set o <- a.extra, oo <- o.AMFO ::  rrm.m[oo])
//   //          == mapThruKlon((set o <- a.extra, oo <- o.AMFO :: oo), rrm);
//   //
//   // assert mapThruKlon(aAMFOs, rrm) == amfosToBeMinusThis;
//
//   //  assert ((set o <- a.extra, oo <- o.AMFO :: oo) + a.extra)   //tnis should not worj!!!
//   //           ==  flattenAMFOs(mapThruKlon(a.extra,rrm));
//
//   reveal AllTheseOwnersAreFlatOK();
//   assert AllTheseOwnersAreFlatOK(rowner); ///this one is OK...
//
//
//
//   var R := rrm.m; //KJX and YEET AGAIN.  WTFFF. clean up!!
//   assert AllMapEntriesAreUnique(R);
//
//   assert klonVMapOK(R);
//
//   assert  (forall x <- R.Keys, oo <- x.AMFO  :: R[oo] in R[x].AMFO);
//
//   assert flattenAMFOs(a.owner) <= R.Keys;
//
//   //
//   //   //these dont work either
//   //   assert (forall o <- a.extra, oo <- R[o].AMFO ::
//   //             && ((oo in rowner.AMFO) || (oo in rextra)))
//   //     ;
//
//   //        assert (forall o <- rextra, oo <- o.AMFO ::
//   //             &&
//   //       ;
//   //
//
//   //assert flatAMFOs == ((set o <- a.extra, oo <- o.AMFO :: oo) + a.extra);
//
// ////KJX  assert rowner.AMFO <= amfosToBeMinusThis;
//
//   reveal AllTheseOwnersAreFlatOK();
//
//   //       var R := rrm.m;
//   //       assert AllMapEntriesAreUnique(R);
//   //       var M := invert(R);
//   //       assert AllMapEntriesAreUnique(M);
//   //
//   //       assert forall r <- R.Keys :: M[R[r]] == r;
//
//
//   //assert (forall o <- rextra :: o.AMFO <=  (rowner.AMFO+rextra));
//   // assert (forall o <- rextra, oo <- o.AMFO :: ((oo in rowner.AMFO) || (oo in rextra)));
//   // assert (forall o <- rextra :: o.AMFO <=  (rowner.AMFO+rextra));
//
//
//   assert Bigfoot(rowner);  //both originally had a .AMFO on the end - do we need it?  yes?  no?  what's the difference?
//   assert AllTheseOwnersAreFlatOK(rowner);
//   assert AllTheseOwnersAreFlatOK(rAMXO);
//
//
//   // assert Bigfoot((rextra), (rowner.AMFO+rextra));
//   // assert AllTheseOwnersAreFlatOK((rextra), (rowner.AMFO+rextra));
//
  var context := rrm.oHeap+rrm.ns;    ///why haul ns in here??? --- cos this the owners for the clone!  - the clowners!
  assert CallOK(rowner, context);

  rrm.calidOKFromCalid();
  assert CallOK(rrm.oHeap);
  CallOKWiderContext(rrm.oHeap, rrm.oHeap, rrm.ns);
  assert CallOK(rrm.oHeap,rrm.oHeap+rrm.ns);

  rrm.calidOKFromCalid();
  assert CallOK(rrm.ns, rrm.oHeap+rrm.ns);

  CallOKWiderFocus(rrm.oHeap, rrm.ns, rrm.oHeap+rrm.ns);
  assert CallOK(rrm.oHeap+rrm.ns, rrm.oHeap+rrm.ns);
  assert CallOK(rrm.oHeap+rrm.ns);
  assert CallOK(context);

FlatAMFOsAreFlat(rowner, rAMXO, rAMXO);
  assert AllTheseOwnersAreFlatOK(rowner, rAMXO);
  assert rAMXO >= flattenAMFOs(rowner);
  //     reveal AllTheseOwnersAreFlatOK();
  // assert AllTheseOwnersAreFlatOK(rowner);//both originally had a .AMFO on the end - do we need it?  yes?  no?  what's the difference?

//TO HERE


    assert forall o <- rowner :: o.Ready() by { reveal CallOK(), COK(); assert CallOK(rowner,context); }
    assert CallOK(rowner, rrm.oHeap+rrm.ns);
    assert CAOKRO: CallOK(rowner, rrm.oHeap+rrm.ns);
    assert CallOK(rrm.oHeap+rrm.ns); //KJX is this redundant Or wouidl it be redundat the other way around???
    // requires AllTheseOwnersAreFlatOK(oo)  //hmm? what would this mean?
    //requires CallOK({oo}+oo.AMFO, context)

    //KJX shouldn't there be some topological restriction on where or when
    //you can create new objects/contexts / regions?
    //what sgoiuld they be?

//  mapThruKlonPreservesAMFO(a.allExternalOwners(), rAMXO, rm);
//  mapThruKlonPreservesAMFO(a.allExternalBounds(), rAMXB, rm);

//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////
print "CALLING MAKE...";
  assert CallOK(rowner, rrm.oHeap+rrm.ns) by { reveal CAOKRO; }



  b := new Object.make(a.fieldModes, rowner, rrm.oHeap+rrm.ns, "clone of " + a.nick, rbound);
print "BACK FROM MAKE with ",fmtobj(b),"\n";
  assert b.fields == map[];

//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

//  mapThruKlonPreservesAMFO(a.allExternalOwners(), rAMXO, rrm);
//  mapThruKlonPreservesAMFO(a.allExternalBounds(), rAMXB, rrm);

  assert fresh(b);
  assert b !in rrm.m.Values;
  assert b !in rrm.ns;
  assert b !in rrm.oHeap;
  assert b.fieldModes == a.fieldModes;
  assert b.owner == rowner;
  assert b.bound == rbound;
  // assert b.owner == mapThruKlon(a.owner, rrm) by { reveal ROWNER_RM; }

  assert b.owner == rowner;

  assert b !in rrm.oHeap;
  assert b !in rrm.m.Values;
  assert a !in rrm.m.Keys;
  assert COK(b, (rrm.oHeap+rrm.ns)+{b});
  // COKWiderContext(b, )
  // assert COK(b, {b} + rrm.oHeap+rrm.m.Values);


  assert b !in rrm.m.Values;
  assert COK(b, rrm.oHeap+rrm.ns+{b});
  assert B_NOTIN: b !in b.owner by {
    reveal COK();
    assert COK(b, rrm.oHeap+rrm.ns+{b});
    assert b.Ready();
    assert b.OwnersValid();
    assert b !in b.owner;
    }
  assert b !in (rrm.oHeap+rrm.ns);

  assert klonVMapOK(rrm.m);
  //assert forall kx <- a.extra :: rrm.m[kx] in b.extra;   //extra not yet cloned


  //extraOK        assert a.extra == {}; //extra not yet cloned
  assert a.allExternalOwners() <= rrm.m.Keys;
  assert a.allExternalBounds() <= rrm.m.Keys;

///PRECOND for putInsife
    assert rrm.calid();
    assert klonVMapOK(rrm.m); //lemma can derive from calid();

    assert canVMapKV(rrm.m,a,b);

        rrm.boundsNestingFromCalid(a,rrm.oHeap);
        assert (a.owner <= a.AMFO);
        assert (a.bound <= a.AMFB);
        assert (a.owner <= rrm.m.Keys+{a});
        assert (a.bound <= rrm.m.Keys+{a});
        assert canVMapKV(rrm.m, a, b);

        assert (a in rrm.oHeap);
        assert (a.AMFO <= rrm.m.Keys+{a});
        assert (a.AMFB <= rrm.m.Keys+{a});
        // assert (mapThruVMapKV(a.AMFO, rrm.m, a, b) == b.AMFO);

        assert rrm.calid();
        assert COK(b, (rrm.oHeap+rrm.ns)+{b});
        reveal COK();
        rrm.boundsNestingFromCalid(b,rrm.oHeap+rrm.ns+{b});

        //    assert (set i <- a.AMFB :: (rrm.m[a:=b])[i]) == b.AMFB;

//         assert (mapThruVMapKV(a.AMFB, rrm.m, a, b) == b.AMFB) by {
//
//
//
// //              assert klonKV(rrm,a,b).fieldMappingsOK(a, b, rrm.m.Keys+{a});
//
//               mapThruKlonPreservesAMFO(a.allExternalOwners(), rAMXO, rm);
//               mapThruKlonPreservesAMFO(a.allExternalBounds(), rAMXB, rm);
//
//               assert a.AMFO == a.allExternalOwners() + {a};
//               assert a.AMFB == a.allExternalBounds() + {a};
//
//               assert b.AMFO == rAMXO + {b};
//               assert b.AMFB == rAMXB + {b};
//         }

//GRR NEEDS to be the KV version               mapThruKlonIsMapThruVMap(a.AMFB, rrm, b.AMFB);
                //  assert b.AMFB == mapThruVMap(a.AMFB, rrm.m);
                //  IfImNotTheExtraKeyTheUnderlyingMapIsFine(a.AMFB,rrm.m,a,b);
                //  assert b.AMFB == mapThruVMapKV(a.AMFB,rrm.m,a,b);
//
//         assert (mapThruVMapKV(a.AMFB, rrm.m, a, b) == b.AMFB) by{
//               assert b.owner == mapThruKlon(a.owner, rrm) by { reveal ROWNER_RM; }
//               assert a !in a.owner;
//               assert b !in b.owner;
//
//     assert rrm.calid();
//     assert a.owner <= rrm.m.Keys;
//     assert a !in rrm.m.Keys;
//     assert a !in a.owner;
//     assert b !in rrm.m.Values;
//     assert canVMapKV(rrm.m, a, b);
//
// IfImNotTheExtraKeyTheUnderlyingMapIsFine(a.owner,rrm.m,a,b);
// //NoKeyNoProblems(a.owner,rrm,a,b);
// assert mapThruVMap(a.owner, rm.m) == mapThruVMapKV(a.owner, rrm.m, a, b);
//         }


        assert a.OwnersValid() by {
                assert unchanged(a);
                assert COK(a, m.oHeap) by { reveal AOK; }
                reveal COK();
                assert a.Ready();
                assert a.OwnersValid();
              }

// //assuage false;
// b := a; return;///FUKOF  //15s

              IfImNotTheExtraKeyTheUnderlyingMapIsFine(a.owner, rm.m, a, b);
              assert a !in a.owner;
//assert mapThruVMapKV(a.owner, rrm.m, a, b) == mapThruVMap(a.owner, rm.m);
              assert b.owner == rowner;
//              assert b.owner  == mapThruKlon(a.owner, rm);
           assert a !in a.owner && b !in a.owner;
//              assert b.owner  == mapThruKlon(a.owner, rrm);


//          asoiosert    b.owner  == mapThruVMap(a.owner, rrm.m)  == mapThruVMapKV(a.owner, rrm.m, a, b);

          assert BROWNER: b.owner  == rowner;
          assert a !in a.owner && b !in b.owner;
          IfImNotTheExtraKeyTheUnderlyingMapIsFine(a.owner, rrm.m, a, b);
//Wed18Dec2024
//           NoKeyNoProblems(a.owner, rrm, a, b) by {
//               assert rrm.calid();
//               assert a.owner <= rrm.m.Keys;
//               assert a.bound <= rrm.m.Keys;
//               assert a !in rrm.m.Keys;
//               assert a !in a.owner;
//               assert a !in a.bound;
//               assert b !in rrm.m.Values;
//
// //not in there ytet,..              assert b in rrm.oHeap+rrm.ns;
//
//               assert klonCanKV(rrm, a, b) by {
//
//                   assert klonVMapOK(rrm.m);
//                   assert canVMapKV(rrm.m,a, b);
//                   assert a in rrm.oHeap;
//                   assert a != b;
//                   assert b !in rrm.oHeap;
//
//                   assert rrm.boundsNestingOK(a, rrm.oHeap);
//                   assert rrm.boundsNestingOK(b, rrm.oHeap+rrm.ns+{b});
//                   assert rrm.boundsNestingOK(a, rrm.oHeap+{a});
//
//                   // assert rrm.fieldMappingsOK(a, b, rrm.m.Keys);
//
//                   assert a.fieldModes == b.fieldModes;
//
//                   assert COK(a, m.oHeap) by { reveal AOK; }
// // assert COK(a, rrm.m.Keys+{a} ) by { reveal AKK; }
//                   rrm.boundsNestingFromCalid(a, rrm.oHeap);
//                   //assuage a.bound <= a.owner;
//                   assert ownerInsideOwner(a.owner, a.bound);
//                   //assuage a.AMFB <= a.AMFO;
//                   assert ownerInsideOwner(a.AMFO, a.AMFB);
//                   //assuage a.bound <= a.AMFB;
//                   assert ownerInsideOwner(a.AMFB, a.bound);
//                   //assuage a.owner <= a.AMFO;
//                   assert ownerInsideOwner(a.AMFO, a.bound);
//                   //assuage a.bound <= a.owner <= rrm.m.Keys;
//                   assert ownerInsideOwnerInsideOwner(rrm.m.Keys, a.owner, a.bound);
//                   //assuage a.AMFB <= a.AMFO   <= rrm.m.Keys;
//                   assert ownerInsideOwnerInsideOwner(m.oHeap, a.AMFO, a.AMFB);
//                   assert (a.AMFO-{a}) <= rrm.m.Keys;
//                   assert (a.AMFB-{a}) <= rrm.m.Keys;
//                   assert ownerInsideOwnerInsideOwner(rrm.m.Keys, a.AMFO-{a}, a.AMFB-{a});
//
//                   assert (a.AMFO) <= rrm.m.Keys+{a};
//
// assert COK(a, m.oHeap) by { reveal AOK; }
// assert COK(a, rrm.oHeap) by { reveal AOK; }
//
// COKNarrowContext(a, rrm.m.Keys+{a}, rrm.oHeap);
// assert COK(a, rrm.m.Keys+{a} );
//
//                   assert klonCanKV(rrm, a, b);
//               }
//
//               NoKeyNoProblems(a.owner, rrm, a, b);
//
//           }
//Wed18Dec2024
              assert rrm.calid();
              assert a.owner <= rrm.m.Keys + {a};
//              assert klonSatanKV(rrm, a, b);jjhhjj
//              assert mapThruKlon(a.owner, rrm)  == mapThruKlonKV(a.owner, rrm, a, b);
          // }

              NoKeyNoProblems(a.owner, rrm, a, b);
              assert rrm.calid();
              assert a.owner <= rrm.m.Keys + {a};
//              assert klonSatanKV(rrm, a, b);

              assert klonCanKV(rrm, a, b);

//          assert mapThruKlon(a.owner, rrm)  == mapThruKlonKV(a.owner, rrm, a, b);


// assert (mapThruVMapKV(a.owner, rrm.m, a, b) == b.owner);


        assert (a.fieldModes == b.fieldModes);


    assert klonCanKV(rrm,a,b);

    var km := klonKV(rrm,a,b); //there it go4s in!

//  var km := rrm.(ns := rrm.ns + nu(a,b)).(m:= VMapKV(rrm.m,a,b));

  print "go4s: ", |km.m|, " ns: ", |km.ns|,"\n";

    assert rrm.calid();
   klonCalidKVCalid(rrm,a,b,km);
//
assert km.calid(); //EVIL  (???? why is this evil?)
//
//     assert km.calid();

// //assuage false;
//b := a; return;///FUKOF  //22s

//
//     assert km.calid() by {
//         reveal km.calid(), km.calidObjects(), km.calidOK(), km.calidMap(), km.calidSheep();
//
//         assert rrm.ns !! rrm.oHeap;
//         assert b !in rrm.oHeap;
//         assert km.ns == (rrm.ns + {b});
//         assert (rrm.ns + {b}) !! rrm.oHeap;
//
//         assert
//             && (km.o in km.oHeap)
//             && (km.m.Keys <= km.oHeap)
//             && (km.ns !! km.oHeap)
//             && (km.m.Values <= km.ns + km.oHeap)
//             && (km.ns <= km.m.Values)
//             ;
//
//         assert
//             && COK(km.o, km.oHeap)
//             && CallOK(km.oHeap)
//             && CallOK(km.m.Keys, km.oHeap) //HMMMM
//             && CallOK(km.m.Values, km.oHeap+km.ns)//HMMMM
//             && CallOK(km.ns, km.oHeap+km.ns) //HMMMM
//             ;
//
//         assert km.calidObjects();
//         assert km.calidOK();
//         assert km.calidMap();
//         assert km.calidSheep();
//         assert km.from(rrm);
//         assert km.calid();
//     }


 // //assuage false;
//b := a; return;///FUKOF  //22s verifies!!

 assert a != b;
 assert km.ns == nu3(rrm.ns,a,b);
 assert km.ns == rrm.ns+nu(a,b);

//not quite shte why we need either of these
 AddToEmptySet(b);
 assert {b} == nu3({},a,b);
 assert nu(a,b) == {b};

//  // //assuage false;
// b := a; return;///FUKOF  //WORKS 45s


    assert km.AreWeNotMen(a, km)  by {
      reveal km.AreWeNotMen();

      assert inside(a,rrm.o);
      assert forall k <- rrm.m.Keys :: rrm.AreWeNotMen(k,rrm);
      assert a !in rrm.m.Keys;
      assert b !in rrm.m.Values;

      assert inside(a,km.o);
      KlonKVExtendsTo(rrm, a, b, km);
      assert forall k <- rrm.m.Keys :: km.m[k] == rrm.m[k];
      assert forall k <- rrm.m.Keys :: rrm.AreWeNotMen(k,rrm);
FORALLAWNMFUCKED(rrm,km);
//      assert forall k <- rrm.m.Keys :: rrm.AreWeNotMen(k,km);

      assert inside(a,km.o);

      assert a in km.m.Keys;
      assert km.m[a] == b;

      assert UniqueMapEntry(km.m,a,b);
      assert UniqueMapEntry(km.m,a);

      assert b in km.ns;
      assert b == km.m[a];
      assert km.m[a] in km.ns;

    assert inside(a,km.o) ==> km.m[a] in km.ns;
    assert inside(a,km.o) ==> UniqueMapEntry(km.m,a);

      assert km.AreWeNotMen(a, km);
    }

//  // //assuage false;
//  b := a; return;///FUKOF  //WORKS 45s

    assert km.AreWeNotMen(a, klonKV(rrm,a,b)) == km.AreWeNotMen(a, km);
    assert km.AreWeNotMen(a, klonKV(rrm,a,b));

assert km.AreWeNotMen(a, km);

    assert a  in rrm.oHeap;
    assert a !in rrm.m.Keys;
    assert b !in rrm.oHeap;
    assert b !in rrm.ns;
    assert b !in rrm.m.Values;
    assert COK(a, rrm.oHeap);
    assert COK(b, rrm.oHeap+rrm.ns+{b});
    assert rrm.m.Keys <= rrm.oHeap;
    assert a.allExternalOwners() <= rrm.m.Keys;
    assert b.allExternalOwners() <= rrm.oHeap+rrm.ns; //need to hae proceessed all owners first;

    assert (a.owner <= rrm.m.Keys);
    // assert (mapThruKlon(a.owner, rrm) == b.owner);

    assert klonVMapOK(rrm.m);

    assert klonCanKV(rrm,a,b);
    assert klonVMapOK(klonKV(rrm,a,b).m);



    assert inside(a,rrm.o);
    assert b.fieldModes == a.fieldModes;


//    assert mapThruKlon(a.owner, rrm) == b.owner;
    assert a !in a.owner;
//    assert mapThruVMapKV(a.owner, rrm.m, a, b) == mapThruVMap(a.owner, rm.m);

// assert b.owner == mapThruVMap(a.owner, rm.m);
// assert b.owner == mapThruKlon(a.owner, rm);
// IfImNotTheExtraKeyTheUnderlyingMapIsFine(a.owner, rm.m, a, b);
// assert (mapThruKlonKV(a.owner, rm, a, b) == b.owner);
// assert (mapThruKlonKV(a.owner, rrm, a, b) == b.owner);

//KJXOWNERS
// assert (mapThruKlon(a.owner, km) == b.owner);

assert a.AMFO == flattenAMFOs(a.owner) + {a};

var amxo := flattenAMFOs(a.owner);
assert  a.AMFO == amxo + {a};
// var other := mapThruKlon(a.owner,km);
// var omxo := mapThruKlon(amxo, km);

///preonditions for mapThruKlonPreservesFlatness3
assert km.calid();
assert a.owner <= km.m.Keys;
assert amxo <= km.m.Keys;
assert amxo == flattenAMFOs(a.owner);
// assert AllTheseOwnersAreFlatOK(amxo);
// assert other == mapThruKlon(a.owner, km);
// assert other == b.owner;  //KJXOWNERS...
// assert  omxo == mapThruKlon(amxo, km);

//  // //assuage false;
// return;///FUKOF  //WORKS 26-34s

// mapThruKlonPreservesFlatness3(a.owner, amxo,
//                     other, omxo, km);


// assert  omxo == flattenAMFOs(other);
// assert  AllTheseOwnersAreFlatOK(omxo);

// assert  mapThruKlonKV({a}, rrm, a, b) == {b};
// mapThruKlonKVisOK({a}, rrm, a, b);

assert  km.m[a] == b;
// mapThruKlonSingleton(a, km);

// assert mapThruKlon({a}, klonKV(rrm, a, b)) == {b};
// assert mapThruKlon({a}, km) == {b};
// assert mapThruKlonKV({a}, rrm, a, b) == {b};

assert b.AMFO == flattenAMFOs(b.owner) + {b};

assert a.allExternalOwners() <= km.m.Keys;
assert {a} <=  km.m.Keys;
assert a.AMFO == a.allExternalOwners() + {a};

assert a.AMFO <= km.m.Keys;
//assert b.AMFO == mapThruKlon(a.AMFO, km);

//mapThruKlonPreservesAMFO2(a,b,km);

//    assert mapThruKlon(a.AMFO, km) == b.AMFO;


//    assert mapThruKlonKV(a.AMFO, rrm, a, b) == b.AMFO;



assert km == klonKV(rrm,a,b);
//assert rrm.AreWeNotMen(a, klonKV(rrm,a,b));
assert klonKV(rrm,a,b).AreWeNotMen(a, klonKV(rrm,a,b));
assert km.AreWeNotMen(a, km);
assert km.AreWeNotMen(a, klonKV(rrm,a,b));
AWNMFUCKED(a, km, rrm);
assert rrm.AreWeNotMen(a, klonKV(rrm,a,b));

// mapThruKlonKVisOK(a.AMFO, rrm, a, b);
//assert mapThruKlonKV(a.AMFO, rrm, a, b) == b.AMFO;


/////////////////////////////////////////////////////////
//  var xm := rrm.putInside(a,b);
    var xm := km.putInside(a,b);
/////////////////////////////////////////////////////////


  assert xm.m == MappingPlusOneKeyValue(rrm.m,a,b);

  assert inside(a, xm.o);
  assert b in xm.ns;
  assert BINNS: b in xm.ns;
  reveal UniqueMapEntry();
  assert (UniqueMapEntry(xm.m,a));

  assert xm.m.Keys >= xm.m.Keys + {a};
  assert xm.m.Values >= xm.m.Values + {b};
  assert COK(b, xm.oHeap+xm.ns);
  assert COKB: COK(b, xm.oHeap+xm.ns);

  MapOKFromCalid(xm);
  assert xm.calid();

  // assert mapThruKlon(a.owner, xm) == b.owner;  //KJXOWNERS
  // assert mapThruKlon(a.AMFO, xm)  == b.AMFO;

  print "Clone_Clone_Clone map updated ", fmtobj(a), ":=", fmtobj(b) ,"\n";



    assert xm.m.Values >= m'.m.Values + {b};
//    assert b.AMFO <= xm.m.Values;  ///TUESDAY14DEC2024
   assert b.AMFO <= xm.oHeap+xm.ns;

//END FUCKOFF
  /////   /////    /////    /////   /////    /////    /////   /////    /////
  /////   preconditiosn for call of Clone_All_Fields
  /////   /////    /////    /////   /////    /////    /////   /////    /////


  assert xm.calid();
  assert COK(a, xm.oHeap);
  assert COK(b, xm.oHeap+xm.ns);
  reveal COK();
  OwnersValidFromCalid(a,xm);
  OwnersValidFromCalid(b,xm);
  assert a.Valid();
  assert a.AllFieldsAreDeclared();

  assert b.fields.Keys == {};
  assert a.fields.Keys <= a.fieldModes.Keys;
  assert a.fieldModes == b.fieldModes;
  assert a in xm.oHeap  ;
  assert a in xm.m.Keys;
  assert b in xm.m.Values;
  assert b in xm.ns;
  assert (a in xm.m.Keys) && xm.m[a] == b;
  assert xm.o    in xm.oHeap;
  assert xm.m.Keys   <= xm.oHeap;


///WHAT THE FUCK FUCKUY FUCK IS GOING ON FUCKY HERE
  // assert (m'.oHeap - m'.m.Keys) >=  (xm.oHeap - xm.m.Keys +{a});
  // assert old((a.fields.Keys)) >= (a.fields.Keys);


  /////   /////    /////    /////   /////    /////    /////   /////    /////
  /////   /////    /////    /////   /////    /////    /////   /////    /////

  assert  xm.o     == m'.o;
  assert  xm.oHeap == m'.oHeap;
  assert  mapLEQ(m'.m,xm.m);
  assert  xm.m.Keys >= m'.m.Keys - {a};

  assert   (m'.oHeap - m'.m.Keys - {a}) >=  (xm.oHeap - xm.m.Keys - {a});
  BiggerIsBigger( (m'.oHeap - m'.m.Keys - {a}), (xm.oHeap - xm.m.Keys - {a}) );
  assert   |m'.oHeap - m'.m.Keys - {a}| >= (|xm.oHeap - xm.m.Keys - {a}|);

assert a.fields.Keys == old(a.fields.Keys);

var left :=  (m'.oHeap - m'.m.Keys - {a});
var right := (xm.oHeap - xm.m.Keys - {a});

assert left >= right;
SetGEQisGTorEQ(left,right);
assert ((left >= right) && not(left > right)) ==> (left == right);

if (left >   right) { assert (left decreases to right); }
   else {
      assert left == right;
      assert a.AMFO ==  a.AMFO;
      assert (a.fields.Keys) == (a.fields.Keys);
      assert 15 > 10;
      assert (
    left,   a.AMFO, (a.fields.Keys), 15
  decreases to
    right, a.AMFO, (a.fields.Keys), 10);
   }


assert (
    left,   a.AMFO, (a.fields.Keys), 15
  decreases to
    right, a.AMFO, (a.fields.Keys), 10);


assert (
    |m'.oHeap - m'.m.Keys - {a}|, |a.AMFO|, |old(a.fields.Keys)|, 15
  decreases to
    |xm.oHeap - xm.m.Keys - {a}|, |a.AMFO|, fielddiff(a,b), 10)
    by
    {
assert |m'.oHeap - m'.m.Keys - {a}|   >=     |xm.oHeap - xm.m.Keys - {a}|;
assert |a.AMFO| >=  |a.AMFO|;
assert |old(a.fields.Keys)| >= fielddiff(a,b);
assert 15 > 10;
assert (
    |m'.oHeap - m'.m.Keys - {a}|, |a.AMFO|, |old(a.fields.Keys)|, 15
  decreases to
    |xm.oHeap - xm.m.Keys - {a}|, |a.AMFO|,  fielddiff(a,b), 10);
    }

assert a.AMFO <= xm.m.Keys;
//assert b.AMFO <= xm.m.Values;  //TUESDAY17DEC2024
assert b.AMFO <= xm.oHeap+xm.ns;


// print "about to call------------------------------\n";
// print "a  ;",a ,"\n";
// print "b  ;",b ,"\n";
// print "xm ;",xm,"\n";
// print "about to call------------------------------\n";

   m := Clone_All_Fields(a,b, xm);

  /////   /////    /////    /////   /////    /////    /////   /////    /////
  /////   /////    /////    /////   /////    /////    /////   /////    /////

  assert m.m.Keys >= xm.m.Keys;
  assert m.m.Values >= xm.m.Values;

  assert m.m.Keys >= m'.m.Keys + {a};
  assert m.m.Values >= m'.m.Values + {b};

  assert b in xm.ns by { reveal BINNS; }
  assert b in m.ns  by { reveal BINNS; }

  assert COK(b, m.oHeap+m.ns) by { reveal COKB; }

  print "RETN Clone_Clone_CLone of ", fmtobj(a), " retuning ", fmtobj(b) ,"\n";

  assert m.m.Values >= m'.m.Values + {b};
}//end Clone_Clone_Clone









































method Clone_All_Owners(a : Object,  m' : Klon)  returns (m : Klon)
  //adds all thers owners of a into the map
//31mins
  decreases |m'.oHeap - m'.m.Keys - {a}|, |a.AMFO|, |a.fields.Keys|, 12

  requires m'.m.Keys <= m'.oHeap
  requires a in m'.oHeap


  requires a !in m'.m.Keys //mustn't have cloned a yet...
  requires COK(a, m'.oHeap)
  requires m'.calid()

  ensures  m.calid()
  //ensures  a !in m.m.Keys //can't ensures this cos an onwer could have a pointer to "a"

  ensures m.from(m')
  ensures a.owner <= m.m.Keys
  ensures a.allExternalOwners() <= m.m.Keys
  ensures mapThruKlon(a.allExternalOwners(),m) <= m.m.Values
     //the above should be OK because it's bascially tautological - huh???
  modifies {}
{
  print "CALL Clone_All_Owner of:", fmtobj(a), " owned by ", fmtown(a.owner) ,"\n";
  print "VARIANT CAO ", |(m'.oHeap - m'.m.Keys - {a})|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 12, "\n";
  print "ENTRY   CAO ", a.owner - m'.m.Keys ," a in Keys ", (a !in m'.m.Keys), "\n";


  var rm := m';
  var b : Object;  //do we care..

  assert rm.from(m');
  reveal rm.calid(),   rm.calidObjects(),   rm.calidOK(),   rm.calidMap(),   rm.calidSheep();
  assert rm.calid() && rm.calidObjects() && rm.calidOK() && rm.calidMap() && rm.calidSheep();

  assert a in rm.oHeap;
  assert COK(a, rm.oHeap);
  reveal COK();
  assert a.AMFO <= rm.oHeap;

  assert forall x <- a.AMFO :: inside(a,x);

  // if (outside(a,rm.o)) {
  //   OutsidersArentMapValues(a,rm);
  //   assert a !in rm.m.Values;
  //   assert a !in rm.m.Keys;
  //   assert not(inside(a, rm.o));
  // }


  assert CallOK(rm.oHeap) by {
    reveal rm.calid(), rm.calidOK();
    assert rm.calid();
    assert rm.calidOK();
    reveal CallOK(), COK();
    assert CallOK(rm.oHeap);
  }


  var xm := rm;
  assert xm.m.Keys >= m'.m.Keys;
  assert mapLEQ(m'.m,xm.m);
  assert xm.from(rm);
  assert xm.from(m');

  assert forall x <- a.AMFO  :: inside(a,x);



  var xo : Object;
  var rr : Object;
  var oldmks  : set<Object>;  //dont fucking ask
  var oldmok :=  false;

  assert !oldmok;
  assert xm == rm;
  assert xm.m.Keys >= (m'.m.Keys);
  assert mapLEQ(m'.m,xm.m);
  assert xm.from(m');

  var MX := a.owner - xm.m.Keys;

      print "PRELOOP ", |MX|," a in Keys ", (a !in xm.m.Keys), "\n";

  while ((MX != {}) && (a !in xm.m.Keys))
    decreases MX
    invariant MX == a.owner - xm.m.Keys
    invariant MX <= a.owner
    invariant forall x <- MX :: inside(a,x)
    invariant xm == rm
    invariant xm.calid()
    invariant rm.calid()
    invariant old(m'.calid())
    invariant xm.from(m')
    invariant MX <= xm.oHeap
    invariant CallOK(xm.oHeap)
    invariant a.owner - {a} <= xm.m.Keys + MX //this one?
    invariant a.owner <= a.AMFO
    invariant oldmok ==> assigned(oldmks)
    invariant oldmok ==> (xm.m.Keys > oldmks)
    invariant m'.oHeap == xm.oHeap
    invariant oldmok ==> ((m'.oHeap - oldmks) > (xm.oHeap - xm.m.Keys))
    invariant xm.m.Keys >= (m'.m.Keys)
    invariant xm.m.Values >= (m'.m.Values)
  {

      print "LOOPTOP ", |MX|," a in Keys ", (a !in xm.m.Keys), "\n";

    assert xm == rm;
    xo :| xo in MX;
    assert xo in MX;
    assert inside(a,xo);

    MX := MX - {xo};

    assert xm.calid();
    assert xo in xm.oHeap;
    COKfromCallOK(xo,xm.oHeap);
    assert COK(xo,xm.oHeap);
    assert xo !in xm.m.Keys;


    assert oldmok ==> (m'.oHeap - oldmks) > (xm.oHeap - xm.m.Keys);

    assert xo in a.AMFO;
    assert a.Ready();
    assert xo in a.owner;
    assert a.AMFO > xo.AMFO;


    assert (m'.oHeap) == m'.oHeap == xm.oHeap;
    assert xm.m.Keys >= (m'.m.Keys);
    assert xm.from(m');

    assert  mapLEQ(m'.m,xm.m) by
    {
      reveal xm.calid(); assert xm.calid();
      reveal xm.calidObjects(); assert xm.calidObjects();
      assert m'.m.Keys <= xm.m.Keys;
      assert m'.m.Values <= xm.m.Values;
      assert m'.m.Keys == m'.m.Keys;
      assert m'.m.Values == m'.m.Values;
      assert xm.m.Keys == xm.m.Keys;
      assert xm.m.Values == xm.m.Values;
      assert m'.m.Keys <= xm.m.Keys;
      assert m'.m.Values <= xm.m.Values;
      assert forall k <- m'.m.Keys :: k in xm.m.Keys;
      assert forall k <- m'.m.Keys :: k in xm.m.Keys && (m'.m[k] == xm.m[k]);
    }


    assert xm.m.Keys > m'.m.Keys;
    assert a !in xm.m.Keys;

    assert ((m'.oHeap - m'.m.Keys)) >= (xm.oHeap - xm.m.Keys);

    assert (|a.AMFO| decreases to |xo.AMFO|);

    assert (|m'.oHeap - m'.m.Keys - {a}|,
            |a.AMFO|,
            |old(a.fields.Keys)|,
            (12)
            decreases to
            |xm.oHeap - xm.m.Keys|,
            |xo.AMFO|,
            |a.fields.Keys|,
            20);

    assert inside(a, xo);


assert (
    |m'.oHeap - m'.m.Keys - {a}|, |a.AMFO|, |old(a.fields.Keys)|, 12
  decreases to
    |xm.oHeap - xm.m.Keys|, |a.AMFO|, |a.fields.Keys|, 20);

    rr, rm := Clone_Via_Map(xo, xm);

    assert rm.m.Keys >= m'.m.Keys;
    assert mapLEQ(m'.m,rm.m);
    assert rm.from(m');

    if (a in rm.m.Keys) {
      m := rm;
       assert m.calidObjects() by {  reveal m.calid(); assert  m.calid();  }
      assert  a in m.m.Keys by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert  a in m.m.Keys by { reveal m.calidObjects(); assert m.calidObjects(); }
      b := m.m[a];
      //

      assert  b in m.m.Values by { reveal m.calidObjects(); assert m.calidObjects();  assert b in m.m.Values; }
      assert  b in m.m.Values by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert m.calidOK() by {  reveal m.calid(); assert  m.calid();  }
      assert  a in m.m.Keys && m.at(a) == b;
      assert  COK(b, m.oHeap+m.ns) by {
        assert b in m.m.Values;
        assert CallOK(m.m.Values, m.oHeap+m.ns) by { reveal m.calidOK(); }
        COKfromCallOK(b, m.m.Values, m.oHeap+m.ns);   }

      assert m.from(m');
      assert  mapLEQ(m'.m,m.m) by
      { reveal m.calidObjects(); assert m.calidObjects();
        assert m'.m.Keys <= m.m.Keys;
        assert mapLEQ(m'.m,m.m);
        assert m'.m.Keys <= m.m.Keys;
        assert m'.m.Values <= m.m.Values;
      }
      assert  m.m.Keys >= m'.m.Keys + {a} by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert  m.m.Values >= m'.m.Values + {b} by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert  m.o == m'.o;
      assert  m.oHeap == m'.oHeap;
      assert  m.ns >= m'.ns;
      assert klonVMapOK(m.m);
      assert forall x <- m.m.Keys, oo <- x.AMFO :: oo in m.m.Keys;
      assert  a in m.m.Keys;
      assert forall oo <- a.AMFO :: oo in m.m.Keys;
      assert a.AMFO <= m.m.Keys;
      assert m.m.Keys == m.m.Keys by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert a.AMFO <= m.m.Keys;
      assert a.owner <= m.m.Keys;
      assert a.allExternalOwners() <= m.m.Keys;

      assert (b.fieldModes == a.fieldModes);

      print "RETN - Clone All Onwers - already clonéd\n";
      return;
    }  // if a is in m.Keys after clone -- if it got added magically...

    assert xo in rm.m.Keys;
    assert xm != rm;

    MX := MX - rm.m.Keys;
    assert rm.m.Keys > xm.m.Keys;
    oldmks := xm.m.Keys;
    oldmok := true;
    xm := rm;
    assert xm.m.Keys >= m'.m.Keys;
    assert xm.m.Keys > oldmks;

    assert MX <= (a.owner - xm.m.Keys);

    assert xm.from(m');

    assert xm == rm;
  } // end loop MX

  m := xm;

  assert a.owner <= m.m.Keys;
  AMFOsFromOwnersFromCalid(a,m);
  assert a.allExternalOwners() <= m.m.Keys;

      print "RETN - Clone All Onwers - done Done DONE\n";

}//END Clone_All_Owners



























method Clone_All_Fields(a : Object, b : Object, m' : Klon)
  returns (m : Klon)
  //clone all fields a.n into b.n
  //a should be preexisting (in m'.oHeapl); b should be "new"  in m'.ns

  decreases |m'.oHeap - m'.m.Keys - {a}|, |a.AMFO|, fielddiff(a,b), 10

  requires MPRIME: m'.calid()
  requires COK(a, m'.oHeap)
  requires COK(b, m'.oHeap+m'.ns)

  requires b.fields.Keys == {}

  requires a.fields.Keys <= a.fieldModes.Keys
  requires a.fieldModes == b.fieldModes


  requires a in m'.oHeap
  requires a in m'.m.Keys

  requires b in m'.m.Values
  requires b in m'.ns
  requires (a in m'.m.Keys) && m'.m[a] == b
  requires m'.o    in m'.oHeap
  requires m'.m.Keys   <= m'.oHeap

  requires a.AMFO <= m'.m.Keys  //seems weird but we are populating m, right...
//  requires b.AMFO == mapThruKlon(a.AMFO, m')  //KJXFRIDAY13TH
//  requires b.AMFO <= m'.m.Values
  requires b.AMFO <= m'.oHeap+m'.ns

  // requires b.fieldModes[n] == Evil //evilKJX this is actually evil
  //well not *that* evil as I still must satisfy refOK
  //
  // requires forall n <- b.fields :: (n in b.fieldModes) &&
  //             AssignmentCompatible(b, b.fieldModes[n], b.fields[n])

  //consequently
  //   requires refOK(a, a.fields[n])

  ensures  m.calid()
  ensures  old(m'.calid())
  ensures  klonVMapOK(m.m)
  ensures  a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...

  //ensures  b.fields.Keys == a.fields.Keys  //FUCK
  ensures a.fieldModes == b.fieldModes

  ensures  a in m.m.Keys
  ensures  (a in m.m.Keys) && m.m[a] == b



  //   ensures  n in b.fields
  //   ensures  (a.fields[n] in m.m.Keys) && m.m[a.fields[n]] == b.fields[n]

  ensures  b in m.m.Values

  ensures  mapLEQ(m'.m,m.m)

  ensures  CallOK(m.oHeap)
  ensures  COK(a, m.oHeap)
  ensures  COK(b, m.oHeap+m.ns)
  ensures  CallOK(m.m.Values, m.oHeap+m.ns)
  ensures  CallOK(m.ns, m.oHeap+m.ns)

  ensures  m.o     == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns    >= m'.ns
  ensures  m.m.Keys    <= m.oHeap


  ensures  unchanged(a)
  ensures  unchanged(m'.oHeap)
  ensures  unchanged(m'.ns - {b})  //will this work?

  ensures  forall x <- (m.m.Values - {b}) :: old(allocated( x )) ==> unchanged( x ) //duesb;t veruft....

  ensures m.from(m')
  //  modifies (set o : Object | o !in m'.oHeap)`fields
  // modifies (set o : Object | o !in ((m'.oHeap+m'.ns) - {b}))`fields
  //or can this  be modifies m'.ns?
  modifies b`fields   ///GGRRR
{
  print "CALL Clone_All_Fields: ", fmtobj(a), " pivot:", fmtobj(m'.o), "\n";

  m := m';

// assert b.AMFO == mapThruKlon(a.AMFO, m');
assert b in m'.m.Values;
assert m'.m[a] == b;  //mmmKJX

//TUESDAY15DEC2024

assert b.AMFO <= (m'.oHeap+m'.ns)
by
   {
      assert COK(b,m'.oHeap+m'.ns);
      reveal COK();
   }

// assert (b.AMFO <= m'.m.Values) by {
//   assert m'.calid() by { reveal MPRIME; }
//   reveal m'.calid(), m'.calidMap();
//   assert m'.calidMap();
//   assert (forall x <- m'.m.Keys ::
//         && m'.boundsNestingOK(m'.m[x], m'.oHeap+m'.ns));
//
//   assert a in m'.m.Keys;
//   assert b in m'.m.Values;
// `  assert COK(b,m'.oHeap+m'.ns);`
//   assert m'.boundsNestingOK(b, m'.oHeap+m'.ns);
//   assert ownerInsideOwnerInsideOwner(m'.oHeap+m'.ns, b.AMFO, b.AMFB);
// }

  assert m'.calid() by { reveal MPRIME; }

  assert BINNS:  b in m.ns;
  print "VARIANT CAF ", |(m'.oHeap - m'.m.Keys) - {a}|, " ", |a.AMFO|, " ", fielddiff(a,b), " ", 10, "\n";
  print "<<<<<<<<<<<\n";
  print "just cloned ", fmtobj(a), " as ", fmtobj(b), "\n";
  print "<<<<<<<<<<<\n";


  assert unchanged(a) && unchanged(m.oHeap);

  assert  m.o == m'.o;
  assert  m.oHeap == m'.oHeap;
  assert  m.ns == m'.ns;
  assert  m.m.Values == m'.m.Values;

  assert  m.m.Keys == m'.m.Keys;
  assert  a in m'.m.Keys;

  assert m.m[a] == b;  //mmmKJX
  // assert (a in m.m.Keys) ==> (m[a] == b);  //mmmKJX

  assert m.calid();
  assert m'.calid() by { reveal MPRIME; }
  assert COK(b, m.oHeap+m.ns);
  assert HEREB: COK(b, m.oHeap+m.ns);




  //assert fresh(b);
  assert  b.fields.Keys == {};
  assert b in m.m.Values;

  //START OF FIELDS…

  print "<<<<<<<<<<<\n";
  printmapping(m.m);
  print "<<<<<<<<<<<\n";

  assert m.calid();
  assert m'.calid() by { reveal MPRIME; }

  var fieldNames : seq<string> := set2seq(a.fields.Keys);

  assert forall k <- a.fields.Keys :: (multiset(a.fields.Keys))[k] == 1;
  assert forall s <- fieldNames :: (multiset(fieldNames))[s] == 1;
  assert forall i | 0 <= i < |fieldNames|, j | 0 <= j < |fieldNames| :: (fieldNames[i] == fieldNames[j]) <==> i == j;
  //assert b.fields.Keys == {};
  assert b.fields.Keys == seq2set(fieldNames[..0]);


  print "Clone_All_Fields fields:", fmtobj(a), " fields=", fmtseqstr(fieldNames), "\n";

  //DOING FIELDS≈≈

  print "BLOOP BLOOP BLOOP\n";

  assert m.calidOK() by {
    assert m.calid();
    reveal m.calid();
    assert m.calidOK();
  }

  assert COK(b, m.oHeap+m.ns);

  assert m'.calid() by { reveal MPRIME; }

  label BLOOP:

  assert m.calidOK();
  reveal m.calidOK();
  assert m.calid();
  assert CallOK(m.ns, m.oHeap+m.ns);
  assert CallOK(m.m.Values, m.oHeap+m.ns);

  assert CallOK(m.m.Keys, m.oHeap) by {}



  var rm := m;

  assert  rm.o     == m.o      == m'.o;
  assert  rm.oHeap == m.oHeap  == m'.oHeap;
  assert  rm.ns    >= m.ns     >= m'.ns;
  assert  rm.m.Values    >= m.m.Values     >= m'.m.Values;
  assert  m.m.Keys     <= rm.m.Keys    <= m.oHeap;


  COKgetsDeclaredFields(a, m.oHeap);
  assert unchanged(a) && unchanged(m.oHeap);
  assert CallOK(m.m.Keys, m.oHeap);

  assert b.fields.Keys == seq2set(fieldNames[..0]) == {};

  for i := 0 to |fieldNames|

    invariant  rm.o     == m.o      == m'.o
    invariant  rm.oHeap == m.oHeap  == m'.oHeap
    invariant  rm.ns    >= m.ns     >= m'.ns
    invariant  rm.m.Values    >= m.m.Values     >= m'.m.Values
    invariant   m.m.Keys    <= rm.m.Keys    <= m.oHeap

    invariant  b in m.ns
    invariant  b in m.m.Values

    invariant COK(a, m.oHeap)
    invariant COK(b, m.oHeap+m.ns)
    invariant mapLEQ(m'.m,m.m)
    invariant a in m.oHeap
    invariant a in m.m.Keys
    invariant m.o in m.oHeap
    invariant CallOK(m.oHeap)
    invariant CallOK(m.m.Keys, m.oHeap)
    invariant CallOK(m.ns, m.oHeap+m.ns)
    invariant CallOK(m.m.Values, m.oHeap+m.ns)
    invariant m.calid()
    invariant old(m'.calid())

    invariant unchanged(a)
    invariant unchanged(m.oHeap)
    //invariant forall x <- m.m.Keys :: (not(inside(x,m.o)) ==> (m.at(x) == x))
    invariant (m'.oHeap - m'.m.Keys +{a}) >= (m.oHeap - m.m.Keys +{a})
    invariant (m'.oHeap - m'.m.Keys) >= (m.oHeap - m.m.Keys)
    invariant b.fields.Keys == seq2set(fieldNames[..i])
    invariant forall i | 0 <= i < |fieldNames|, j | 0 <= j < |fieldNames| :: (fieldNames[i] == fieldNames[j]) <==> i == j

    invariant  m.m[a] == b
    invariant  a.fieldModes == b.fieldModes
    invariant  a.AllFieldsAreDeclared()


    invariant old(m'.calid())
  {
    assert b.fields.Keys == seq2set(fieldNames[..i]);

    assert COK(b, m.oHeap+m.ns);

    var n : string := fieldNames[i];
    var ofv : Object := a.fields[n];

    assert n !in seq2set(fieldNames[..i]);

    assert (n !in b.fields.Keys) by {
      assert n !in seq2set(fieldNames[..i]);
      assert b.fields.Keys == seq2set(fieldNames[..i]);
      assert (n !in b.fields.Keys);
    }

    print "  TLOOP  ",fmtobj(a),".",n," :=", fmtobj(ofv), "\n";
    print "  TLOOP  (recurse on field ",n,")\n";
    print "  TLOOP m:", |m.oHeap - m.m.Keys|, " m':", |m'.oHeap - m'.m.Keys|, "\n";
    print "  TLOOP b.fieldsKeys==", b.fields.Keys, "\n";
    print "  TINV                ", fieldNames[..i], "\n";
    print "  TLOOPINV            ",seq2set(fieldNames[..i]),"\n";


    print "VARIANT*CAF ", |(m.oHeap - m.m.Keys) - {a}|, " ", |a.AMFO|, " ", fielddiff(a,b), " ", 10, "\n";


    //   assert (m.oHeap - m.m.Keys) < (m'.oHeap - m'.m.Keys);

    assert  rm.o     == m.o      == m'.o;
    assert  rm.oHeap == m.oHeap  == m'.oHeap;
    assert  rm.ns    >= m.ns     >= m'.ns;
    assert  rm.m.Keys    >= m.m.Keys     >= m'.m.Keys;
    assert  rm.m.Values    >= m.m.Values     >= m'.m.Values;
    assert  m.m.Keys     <= rm.m.Keys    <= m.oHeap;

    assert b in m.ns by { reveal BINNS; assert b in m.ns; }
    assert n !in b.fields;
    assert refOK(a, a.fields[n])
    by {
      assert m.calid();  reveal m.calid();
      assert m.calidOK(); reveal m.calidOK();
      assert COK(a,m.oHeap); reveal COK();
      assert a.AllOutgoingReferencesAreOwnership(m.oHeap);
      assert  refOK(a, a.fields[n]);
      // - inside(f,t.owner);
    }

    assert a.AllFieldsAreDeclared();
    assert a.fields.Keys <= a.fieldModes.Keys;
    assert a.fieldModes == b.fieldModes;
    assert n in b.fieldModes;


    assert forall n <- b.fields ::
        && (n in b.fieldModes)
        && AssignmentCompatible(b, b.fieldModes[n], b.fields[n])
    by {
      assert m.calid();
      reveal m.calid();

      assert old(m'.calid());

      assert COK(b, m.oHeap+m.ns);
      reveal COK();
      assert b.Valid();
      assert b.AllFieldsContentsConsistentWithTheirDeclaration();
      assert forall n <- b.fields ::
          AssignmentCompatible(b, b.fieldModes[n], b.fields[n]);
    }

    var OLDFLDS := b.fields.Keys;

    assert b in m.ns;
    assert b in m.m.Values;
    assert a in m.m.Keys;



    var v_caf := ((m'.oHeap - m'.m.Keys +{a}), a.AMFO, (a.fields.Keys), 10);
    var v_cfm := ((m.oHeap - m.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Clone_Field_Map

    print "v_caf ", v_caf, "\n";
    print "v_cfm ", v_cfm, "\n";

    assert b.fields.Keys == seq2set(fieldNames[..i]);
    assert a.fields.Keys == seq2set(fieldNames);

    print "okaoka ", (m'.oHeap - m'.m.Keys +{a}) >  (m.oHeap - m.m.Keys +{a}), "\n";
    print "okaoka ", (m'.oHeap - m'.m.Keys +{a}) == (m.oHeap - m.m.Keys +{a}), "\n";

    assert (m'.oHeap - m'.m.Keys +{a}) >= (m.oHeap - m.m.Keys +{a});
    assert a.AMFO >= a.AMFO;
    assert (a.fields.Keys) >= (a.fields.Keys - b.fields.Keys);
    assert 10 > 5;

    label B4CLONEFIELD:

    assert  old(m'.calid());

//////////////////////////////////////////////////////
//preconditions for Clone_Field_Map(a,n,b,m);
//////////////////////////////////////////////////////

  assert m.calid();
  assert COK(a, m.oHeap);
  assert COK(b, m.oHeap+m.ns);

  assert n  in a.fields.Keys;
  assert n !in b.fields.Keys;

  assert n  in a.fieldModes;
  assert n  in b.fieldModes;
  assert a.fieldModes == b.fieldModes;
  assert FLDMODZ: a.fieldModes == b.fieldModes;



  assert a in m.oHeap;
  assert a in m.m.Keys;
  assert a.AMFO <= m.m.Keys;

  assert b in m.ns;
  assert b in m.m.Values;
//  assert b.AMFO <= m.m.Values;
//  assert b  in m.oHeap+m.ns; //TUESDAY17DEC2024
  assert b.AMFO <= m.oHeap+m.ns; //FUUUK - THU27FEB2025

  assert (a in m.m.Keys) && m.m[a] == b;
  assert m.o    in m.oHeap;
  assert m.m.Keys   <= m.oHeap;

  assert forall n <- b.fields :: (n in b.fieldModes) && AssignmentCompatible(b, b.fieldModes[n], b.fields[n]);
  assert refOK(a, a.fields[n]);

print "WHOOPS-> ", |m'.oHeap - m'.m.Keys +{a}|, " ", |a.AMFO|," ",|a.fields.Keys - b.fields.Keys|," 10\n";
print "->WHOOPS ", |m'.oHeap - m'.m.Keys +{a}|, " ", |a.AMFO|," ",|a.fields.Keys - b.fields.Keys|," 5 \n";



assert (
    |m'.oHeap - m'.m.Keys - {a}|, |a.AMFO|, old(fielddiff(a,b)), 10
  decreases to
    |m.oHeap - m.m.Keys - {a}|, |a.AMFO|, fielddiff(a,b), 5
 );

///  decreses (m'.oHeap - m'.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 10 //Clone_All_Fields
///  decreases (m'.oHeap - m'.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5 //Clone_Field_Map
//////////////////////////////////////////////////////
//////////////////////////////////////////////////////


//INSTEAD OF m that was the BIG BUG
    rm := Clone_Field_Map(a,n,b,m);
// rm := m;
// assuage b.fields.Keys == OLDFLDS + {n};

    assert b.fields.Keys == OLDFLDS + {n};

//////////////////////////////////////////////////////
//////////////////////////////////////////////////////

    assert  old(m'.calid());

    assert  rm.o     == m.o      == m'.o;
    assert  rm.oHeap == m.oHeap  == m'.oHeap;
    assert  rm.ns    >= m.ns     >= m'.ns;
    assert  rm.m.Keys    >= m.m.Keys     >= m'.m.Keys;
    assert  rm.m.Values    >= m.m.Values     >= m'.m.Values;
    assert  m.m.Keys     <= rm.m.Keys    <= m.oHeap;

    //   assert old@B4CLONEFIELD(forall x <- m'.m.Keys :: x.fieldModes == m'.m[x].fieldModes);
    //   assert (forall x <- m'.m.Keys :: x.fieldModes == old@B4CLONEFIELD(x.fieldModes));
    //   assert (forall x <- m'.m.Keys :: m'.m[x].fieldModes == old@B4CLONEFIELD(m'.m[x].fieldModes));
    //   assert (forall x <- m'.m.Keys :: x.fieldModes == m'.m[x].fieldModes);
    //

    assert n == fieldNames[i];
    assert n in b.fields.Keys;
    assert b.fields.Keys == OLDFLDS + {n};


    nqf(n,fieldNames[i]);

    assert {n} == {fieldNames[i]} == seq2set([ n ]) == seq2set([ fieldNames[i] ]);
    assert {n} == {fieldNames[i]} == seq2set([ fieldNames[i] ]);

//    invariant  b.fields.Keys == seq2set(fieldNames[..i])

    extendSeqSet(fieldNames, i);

  assert  seq2set(fieldNames[..i+1]) == seq2set(fieldNames[..i]) + seq2set([fieldNames[i]]);

  assert  seq2set(fieldNames[..i+1]) == seq2set(fieldNames[..i]) + seq2set([n]);

  assert b.fields.Keys == seq2set(fieldNames[..i+1]);


//    assert b.fields.Keys == seq2set(fieldNames[..i]) + seq2set([fieldNames[i]]);

//    assert b.fields.Keys == seq2set(fieldNames[..(i+1)]);

    // assert fieldNames[..i] + [fieldNames[i]] == fieldNames[..i+1];
    // assert b.fields.Keys == seq2set(fieldNames[..i]) + seq2set([fieldNames[i]]);
    // assert b.fields.Keys == seq2set(fieldNames[..i+1]);

    assert rm.from(m);
    //assert m.from(m');
    //assert rm.from(m');


    assert rm.calid();
    //  assert COK(b, m.oHeap+m.ns );
    m := rm;
    assert m.calid();
    assert old(m'.calid());

    //  by {
    //    reveal MPRIME; reveal m.calid();
    //
    //    assert m' == m';
    //    assert mapLEQ(m'.m, m.m);
    //
    //    assert forall k <- m'.m.Keys :: m'.m[k] == m.m[k];
    //    assert forall k <- m'.m.Keys :: m'.m[k].fields == m.m[k].fields;
    //    assert forall k <- m'.m.Keys :: m'.m[k] == m.m[k];
    //    assert forall k <- m'.m.Keys :: m'.m[k].fields == m.m[k].fields;
    //
    //             reveal m'.calid();
    // //            assert m'.calid();
    //
    //         assert (m'.o in  m'.oHeap);
    //         assert (m'.m.Keys <= m'.oHeap);
    //         assert (m'.m.Values <= m'.oHeap+m'.ns);
    //         assert COK(m'.o, m'.oHeap);
    //         assert CallOK(m'.oHeap);
    //         assert CallOK(m'.m.Keys, m'.oHeap);
    //
    //         assert CallOK(m'.m.Values-{b}, m'.oHeap+m'.ns) by
    //           {
    //
    //           }
    //
    //         assert CallOK(m'.ns-{b}, m'.oHeap+m'.ns) by
    //           {
    //
    //           }
    //
    //         // assert CallOK(m'.m.Values, m'.oHeap+m'.ns);
    //         // assert CallOK(m'.ns, m'.oHeap+m'.ns);
    //
    //             reveal m'.calidOK();
    //             assert m'.calidOK();
    //             reveal m'.calidObjects();
    //             // assert m'.calidObjects();
    //             reveal m'.calidMap();
    //             // assert m'.calidMap();
    //             assert m'.m.Keys == m'.m.Keys;
    //
    //         reveal m'.AreWeNotMen();
    //         //reveal UniqueMapEntry();
    //
    //         assert (forall x <- m'.m.Keys :: m'.AreWeNotMen(x, m'));
    //         assert (forall x <- m'.m.Keys :: x.fieldModes == m'.m[x].fieldModes);
    //         assert AllMapEntriesAreUnique(m'.m);
    //
    //             reveal m'.calidSheep();
    //             assert m'.calidSheep();
    //
    //    assert m'.calid(); }
    //


    assert  CallOK(m.m.Keys, m.oHeap)
    by { reveal m.calid();    assert m.calid();
         reveal m.calidOK();  assert m.calidOK();
       }
  } //end of loop

  assert unchanged(a) && unchanged(m.oHeap);


  //DONE FIELDS

  assert COK(b, m.oHeap+m.ns) by { reveal HEREB; }
  assert mapLEQ(m'.m,m.m);
  //
  // assert m'.calid() by { reveal MPRIME; }

  reveal m.calid();
  assert m.calid();
  reveal m.calidObjects();
  assert m.calidObjects();

  reveal m.calidMap(); assert m.calidMap();
  reveal m.calidSheep(); assert m.calidSheep();


  assert m.m[a] == b;

  assert m.at(a) == b;
  assert a in m.m.Keys;
  assert b in m.oHeap+m.ns;

  assert COK(b, m.oHeap+m.ns);

  assert mapLEQ(m'.m,m.m);


  assert CallOK(m.oHeap);
  assert COK(a, m.oHeap);
  assert COK(b, m.oHeap + m.ns);
  assert CallOK(m.m.Values, m.oHeap+m.ns);
  assert COK(b, m.oHeap  + m.ns);


  reveal m.calidObjects(); assert m.calidObjects();


  assert COK(m.o, m.oHeap);
  assert CallOK(m.oHeap);
  assert CallOK(m.m.Keys, m.oHeap);
  assert CallOK(m.m.Values, m.oHeap+m.ns);
  assert CallOK(m.ns, m.oHeap+m.ns);

  reveal m.calidOK(); assert m.calidOK();

  reveal m.calidMap(); assert m.calidMap();

  assert klonVMapOK(m.m);



  assert  rm.o     == m.o      == m'.o;
  assert  rm.oHeap == m.oHeap  == m'.oHeap;
  assert  rm.ns    >= m.ns     >= m'.ns;
  assert  rm.m.Values    >= m.m.Values     >= m'.m.Values;

  reveal m.calidObjects(); assert m.calidObjects();
  reveal m.calidOK(); assert m.calidOK();
  reveal m.calidSheep(); assert m.calidSheep();

  assert m.m.Keys == m.m.Keys;

  reveal m.AreWeNotMen();
  assert forall x <- m.m.Keys :: m.AreWeNotMen(x, m);
  assert forall x <- m.m.Keys :: (not(inside(x,m.o)) ==> (m.m[x] == x));

  assert  b.fieldModes == a.fieldModes;

  reveal m.calid(); assert m.calid();

  // assert m'.calid() by { reveal MPRIME; }

  assert klonVMapOK(m.m) && a.AMFO <= m.m.Keys;
  assert unchanged(a) && unchanged(m.oHeap);
  //
  //     assert m'.calid() by {
  //        assert unchanged(m'.m.Keys);
  //        assert unchanged(m'.m.Values - {b});
  //        //assuage COK(b, m.oHeap + m.ns);
  //        //assuage m'.m.Values - {b} + {b} == m'.m.Values;
  // //       assert
  //        assert CallOK(m'.m.Values, m.oHeap + m.ns);
  //
  //         assert m'.calidObjects();
  //         assert m'.calidOK();
  //         assert m'.calidMap();
  //         assert m'.calidSheep();
  //
  //
  assert old(m'.calid());
  //     }
  print "RETN Clone_All_Fields done ", fmtobj(a), "\n";

  return;
}
//end Clone_All_Fields






//
//
// lemma extendSeq<T>(ss : seq<T>, n : nat)
//     requires n < |ss|
//     ensures  ss[..n+1] == ss[..n] + [ss[n]]
// {}
//
//
//  lemma extendSeqSet<T>(ss : seq<T>, n : nat)
//     requires n < |ss|
//     ensures  seq2set(ss[..n+1]) == seq2set(ss[..n]) + seq2set([ss[n]])
// {}
//
//  lemma singletonSeqSet<T>(ss : seq<T>, n : nat)
//     requires n < |ss|
//     ensures  {ss[n]} == seq2set([ ss[n] ])
// {}
//
//
// lemma nqf<T>(a : T, b : T)
//     requires a == b
//     ensures  {a} == {b} == seq2set([ a ]) == seq2set([ b ])
//  {}








method Clone_Field_Map(a : Object, n : string, b : Object, m' : Klon)
  returns (m : Klon)
  //clone field a.n into b.n
  //a should be preexisting (in m'.oHeapl); b should be "new" (in m'.ns)

  decreases |m'.oHeap - m'.m.Keys - {a}|, |a.AMFO|, fielddiff(a,b), 5 //Xlone_Field_Map

  requires (|m'.oHeap| - |m'.m.Keys| + |{a}|, |a.AMFO|, fielddiff(a,b), 10
    decreases to |m'.oHeap| - |m'.m.Keys| + |{a}|, |a.AMFO|, fielddiff(a,b), 5)

  requires MPRIME: m'.calid()
  requires COK(a, m'.oHeap)
  requires COK(b, m'.oHeap+m'.ns)
  requires COKbm': COK(b, m'.oHeap+m'.ns)

  requires n  in a.fields.Keys
  requires n !in b.fields.Keys

  requires n  in a.fieldModes
  requires n  in b.fieldModes
  requires a.fieldModes == b.fieldModes
  requires FLDMODZ: a.fieldModes == b.fieldModes


  requires a in m'.oHeap
  requires a in m'.m.Keys
  requires a.AMFO <= m'.m.Keys //KJX should be part of some invariant

  requires b in m'.ns
  requires b in m'.m.Values
//  requires b.AMFO <= m'.m.Values //KJX should be part of some invariant - also
//  assert b  in m.oHeap+m.ns; //TUESDAY17DEC2024
  requires b.AMFO <= m'.oHeap+m'.ns  //FUUUK - THU27FEB2025

  requires (a in m'.m.Keys) && m'.m[a] == b
  requires m'.o    in m'.oHeap
  requires m'.m.Keys   <= m'.oHeap


    //not sure why I'd need this..
  requires forall n <- b.fields :: (n in b.fieldModes) &&
                                   AssignmentCompatible(b, b.fieldModes[n], b.fields[n])

  //consequently
  requires refOK(a, a.fields[n])



  ensures  b.fields.Keys == old(b.fields.Keys) + {n}
  ensures  (a.fields.Keys - b.fields.Keys) < old(a.fields.Keys - b.fields.Keys)
  ensures  m.calid()
  ensures  old(m'.calid())


  ensures  a in m.m.Keys
  ensures  (a in m.m.Keys) && m.m[a] == b

  ensures  n in b.fields
  ensures  (a.fields[n] in m.m.Keys) && m.m[a.fields[n]] == b.fields[n]

  ensures  b in m.m.Values

  ensures  mapLEQ(m'.m,m.m)

  ensures  CallOK(m.oHeap)
  ensures  COK(a, m.oHeap)
  ensures  COK(b, m.oHeap+m.ns)
  ensures  CallOK(m.m.Values, m.oHeap+m.ns)
  ensures  CallOK(m.ns, m.oHeap+m.ns)

  ensures  m.o     == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns    >= m'.ns
  ensures  m.m.Keys    >= m'.m.Keys
  ensures  m.m.Values    >= m'.m.Values
  ensures  m.m.Keys    <= m.oHeap


  ensures klonVMapOK(m.m)
  ensures a.AMFO <= m.m.Keys // shoulnd't that be requires

  ensures old(m'.calid())
  ensures m.from(m')

  ensures a.fieldModes == b.fieldModes

  ensures  unchanged(a)
  ensures  unchanged(m'.oHeap)
  ensures  unchanged(m'.m.Values - {b})
  ensures  unchanged(m'.m.Keys)

  //ensures  a !in m'.m.Keys ==> b !in m'.ns  //KJX sure about this?
  //  in this case, a should be in kis, b in b',ns

  ensures  unchanged(m'.ns - {b})  //will this work?

  //  ensures unchanged(m.m.Values - {b}) //duesb;t veruft....

  //  modifies (set o : Object | o !in m'.oHeap)`fields
  // modifies (set o : Object | o !in ((m'.oHeap+m'.ns) - {b}))`fields
  //or can this  be modifies m'.ns?
  modifies b`fields
{

var OLDFIELDDIFFAB := fielddiff(a,b);

print "CALL Clone_Field_Map ", fmtobj(a), " «", n, "»\n";
print "VARIANT CFM ", |m'.oHeap - m'.m.Keys - {a}|, " ", |a.AMFO|, " ", fielddiff(a,b), " ", 5, "\n";


  assert m'.calid() by { reveal MPRIME; }
  assert unchanged(m'.ns);

  assert klonOwnersAreCompatible(a, b, m') by {
      reveal m'.calid(), m'.calidObjects(), m'.calidOK(), m'.calidMap(), m'.calidSheep();
      assert m'.calidObjects() && m'.calidOK() && m'.calidMap() && m'.calidSheep() && m'.calid();
      assert klonOwnersAreCompatible(a, b, m');
    }

  m := m';

assert m.from(m');
//SPLURGE
assert (m.calid()) by
{
  reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep();
  assert m.calidObjects() && m.calidOK() && m.calidMap() && m.calidSheep() && m.calid();
}
assert klonOwnersAreCompatible(a, b, m);
//END SPLURGE



  var v_cfm := ((m.oHeap - m.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Clone_Field_Map *variant for decreases clause*

  var onb := m.ns - {b};
  var ctx := (m.oHeap+m.ns);

  assert CallOK(onb, ctx) by
  {
    assert m.calid(); reveal m.calid(); reveal m.calidOK();
    assert CallOK(m.ns, m.oHeap+m.ns);
    CallOKNarrowFocus(onb, m.ns, m.oHeap+m.ns);
    assert CallOK(onb, m.oHeap+m.ns);
  }

  assert CallOK(m.oHeap) by {
    assert m.calid(); reveal m.calid();
    assert m.calidOK(); reveal m.calidOK();
    assert CallOK(m.oHeap);
  }

  assert m.calid();
  assert old(m'.calid());
  assert unchanged(m'.ns);

  OutgoingReferencesWithinKlonHeapFromCalid(m);
  assert forall x <- m.oHeap :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(m.oHeap);

  assert a in m.oHeap;
  assert a.Ready();
  assert a.AllOutgoingReferencesWithinThisHeap(m.oHeap);

  var ofv := COKat(a,n,m.oHeap);

  label B3:
  assert m'.calid() by { reveal MPRIME; }


assert a in m'.m.Keys;
assert a in m.m.Keys;

  print "VARFROM ", |m'.oHeap - m'.m.Keys  - {a}|, " ", |a.AMFO|, " ", OLDFIELDDIFFAB, " ", 5, "\n";

  print "VARFTO  ", |m.oHeap - m.m.Keys|, " ", |a.AMFO|, " ", |(a.fields.Keys )|, " ", 20, "\n";

assert old(fielddiff(a,b)) == OLDFIELDDIFFAB;

assert (
    |m'.oHeap - m'.m.Keys - {a}|, |a.AMFO|, OLDFIELDDIFFAB, 5
  decreases to
    |m.oHeap -  m.m.Keys|, |a.AMFO|, |a.fields.Keys|, 20
 );

  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
  var rfv, rm := Clone_Via_Map(ofv, m);
  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //

  label B3X:
  assert rm.calid();
  assert rm.from(m);
  assert klonVMapOK(rm.m);
  assert rm.m[ofv] == rfv;

  assert RFVCOK: COK(rfv, rm.oHeap+rm.ns) by {
    assert rfv in rm.m.Values;
    rm.calidOKFromCalid();
    assert CallOK(rm.m.Values, rm.oHeap+rm.ns);
    COKfromCallOK(rfv, rm.m.Values, rm.oHeap+rm.ns);
  }

  m := rm;

  //SPLURGE
  assert (m.calid()) by
  {
    reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep();
    assert m.calidObjects() && m.calidOK() && m.calidMap() && m.calidSheep() && m.calid();
  }
  //END SPLURGE

  assert unchanged(m'.ns);

//   assert m'.calid() by { reveal MPRIME; }
//
//   assert unchanged@B3(m'.oHeap);


  assert rfv in  m.m.Values;
  // assert rfv in  m.oHeap+m.ns;   //let's see if we need these bits.
  // assert COK(rfv,m.oHeap+m.ns);

//////ensure cloned field is refOK ////////////

  assert m.calid();
  assert {a,ofv} <= m.m.Keys;
  assert b == m.m[a];
  assert rfv == m.m[ofv];

  assert a in m.m.Keys;
  assert b == m.m[a];

  klonOwnersAreCompatibleWider(a,b,m',m);
  assert klonOwnersAreCompatible(a, b, m);
  assert klonOwnersAreCompatible(ofv, rfv, m);
  assert refOK(a,ofv);

  // assert m.boundsNestingOK(a, m.oHeap);
  // assert m.boundsNestingOK(b, m.oHeap+m.ns);
  // assert (b.AMFO >= b.AMFB >= a.AMFB);
  //
klonFieldsAreCompatible(a,ofv,b,rfv,m);
//
//   assert refOK(a, ofv);
//
// if (outside(ofv,m.o)) {
// //
// //
//
//           assert
//             (&& klonOwnersAreCompatible(a, b, m)
//              && klonOwnersAreCompatible(ofv, rfv, m))
//           by {
//
//
//               assert klonAllOwnersAreCompatible(m);
//               assert b == m.m[a];
//               assert klonOwnersAreCompatible(a, b, m);
//               assert rfv == m.m[ofv];
//               assert klonOwnersAreCompatible(ofv, rfv, m);
//           }
//
//
//   assert (b.AMFO >= b.AMFB >= a.AMFB);
//   assert (rfv.AMFO >= rfv.AMFB >= ofv.AMFB);
//
//   assert refOK(a, ofv);
//   assert boundInsideOwner(a,ofv) || directlyInside(ofv,a);
//
//   if (boundInsideOwner(a,ofv)) {
//       assert a.AMFB >= (ofv.AMFO - {ofv});
//
//       assert b.AMFB >= (rfv.AMFO - {rfv});
//       assert boundInsideOwner(b,rfv);
//   } else {
//       assert directlyInside(ofv,a);
//       assert a.AMFO == (ofv.AMFO - {ofv});
//
//
//       assert b.AMFO == (rfv.AMFO - {rfv});
//       assert directlyInside(rfv,b);
//   }
//
//   assert boundInsideOwner(b,rfv) || directlyInside(rfv,b);
//   assert refOK(b, rfv);
//
// }//end outside case
//
//
//
//   assert boundInsideOwner(a, ofv) || directlyInside(ofv,a);
//   // mapThruKlonPreservesBoundInsideOwner(a, ofv, b, rfv, m);  //KJXFRIDAY13THK
// //  assert klonRefOK(a, ofv, b, rfv, m);
//
//   assert boundInsideOwner(b, rfv) || directlyInside(rfv, b);

  assert refOK(b, rfv);

//////END ensure cloned field is refOK ////////////



//print "ASSUMING ASSIGNMENT COMPATIBLE\n";
        assume AssignmentCompatible(b, b.fieldModes[n], rfv);
//print "ASSUMING ASSIGNMENT COMPATIBLE\n";


//   assert AssignmentCompatible(b, b.fieldModes[n], rfv)
//   by {
//     // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
//
//     assert b.fieldModes[n] == a.fieldModes[n];
//
//     assert AssignmentCompatible(a, a.fieldModes[n], a.fields[n]) by
//     {
//       reveal COK();
//       assert COK(a, m.oHeap);
//       assert a.Valid();
//       assert a.AllFieldsContentsConsistentWithTheirDeclaration();
//       assert forall n <- a.fields.Keys :: AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);
//       assert AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);
//     }
//
//
//
//     match (b.fieldModes[n]) {
//       case Evil =>
//         assert b.fieldModes[n] == Evil;
//         EVILisCompatibleWithAnything(b,rfv);
//         assert AssignmentCompatible(b, b.fieldModes[n], rfv);
//
//       case Rep | Owned(_) | Loaned(_) =>
//         assert AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);
//         assert ofv == a.fields[n];
//      //   assert ofv.owner == a; //KJX what should this be>?
//         assert b == m.m[a];
//         assert rfv == m.m[ofv];
//      //   assert b == rfv.owner;
//         // assert b == m.m[a.fields[n].owner];
//         // assert b == rfv.owner;
//         // mapThruKlonPreservesInside(ofv,a, rfv, b, m);   //KJXFRIDAY13TH
//         assert AssignmentCompatible(b, b.fieldModes[n], rfv);
//
//       case Peer =>
//         assert AssignmentCompatible(a, a.fieldModes[n], ofv);
//         assert a.owner == ofv.owner;
//
//
//           assert COK(a, m.oHeap);
//           RVfromCOK(a, m.oHeap);
//           assert a.OwnersValid();
//           assert a.owner <= a.AMFO <= m.m.Keys;
//
//           assert klonVMapOK(m.m);
//           assert m.m[a] == b;
//           // assert (mapThruKlon(a.owner, m) == b.owner);  //KJXOWNERS mapthru KLon.
//           // assert m.m[ofv] == rfv;
//           // assgert mapThruKlon(ofv.owner, m) == rfv.owner;  //KJXOWNERS
//
//           assert b.owner == rfv.owner; //WORK THE FOKKA?
//
//           //assuage b.owner == rfv.owner;   //KJXOWNERS
//
//         assert AssignmentCompatible(b, b.fieldModes[n], rfv);
//t
//       case Borrow(pp,bb,nn,ff) =>
//         assert refOK(a,a.fields[n]);
//         assert refOK(b,rfv);
//         assert AssignmentCompatible(b, b.fieldModes[n], rfv);
//     }



    // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
    // }




  assert m.calid();

  assert b in m.ns;

assert (b !in m.oHeap) by {

  reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep();
  assert m.calidObjects() && m.calidOK() && m.calidMap() && m.calidSheep() && m.calid();

    bNotInoHeap(b,m);
    }

  label B4:

  assert m.calidOK() by { reveal m.calid(); }
  assert m'.calid() by { reveal MPRIME; }
  assert m.calid() by {  reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep(); }


  assert COK(b, rm.oHeap+rm.ns) by
  {
    assert b in m'.ns;
    assert b in m.ns;
    assert COK(b, m'.oHeap+m'.ns);
    assert m'.ns <= m.ns;
    COKWiderContext2(b,m'.oHeap+m'.ns,m.oHeap+m.ns);
    assert COK(b, m.oHeap+m.ns);
  }

assert COKB4: COK(b, rm.oHeap+rm.ns);

  assert
    && CallOK(m.m.Values, m.oHeap+m.ns)
    && CallOK(m.ns, m.oHeap+m.ns)
    && ( m.m.Keys    <= m.oHeap )
  by { reveal m.calid(); reveal m.calidOK(); }

  CallOKNarrowFocus(m.m.Values-{b}, m.m.Values, m.oHeap+m.ns);
  CallOKNarrowFocus(m.ns-{b}, m.ns, m.oHeap+m.ns);

  assert CallOK(m.m.Values-{b}, m.oHeap+m.ns);
  assert CallOK(m.ns-{b}, m.oHeap+m.ns);

  assert b in m.ns;

  label JUSTBEFORE:



  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //

//  b.fields := b.fields[n := rfv];


  assert COK(rfv, m.oHeap+m.ns) by { reveal RFVCOK; }
  m.COKput(b, m.oHeap+m.ns, n, rfv);
  assert b.fields == old(b.fields)[n := rfv];
  assert COK(b, m.oHeap+m.ns);

  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //


  assert unchanged(m'.ns - {b});

  assert CallOK(m.m.Values-{b}, m.oHeap+m.ns);
  assert CallOK(m.ns-{b}, m.oHeap+m.ns);
  assert Call_NOB: CallOK(m.ns-{b}, m.oHeap+m.ns);


  assert m.m[ofv] == rfv;
  assert rfv in m.m.Values;
  assert rfv in m.oHeap+m.ns;


  if (b != rfv) {

    assert rfv in (m.oHeap+m.ns);
    if (rfv in m.oHeap)
       {
        assert unchanged(m.oHeap);
        assert unchanged(rfv);
       } else {
        assert rfv !in m.oHeap;
        assert rfv in m.ns;
        assert unchanged(m'.ns - {b});
        assert rfv != b;
        assert unchanged@B3X(rfv);
       }
    assert unchanged@B3X(rfv);
    assert COK(rfv, rm.oHeap+rm.ns) by { reveal RFVCOK; }

//    assert rm == m;
//    assert rm.from(m);  //HOW ODD

    // m'.calidOKFromCalid();
    // COKfromCallOK(rfv,m.m.Values, m.oHeap+m.ns);
    // assert COK(rfv,m.oHeap+m.ns);

    assert COK(b,  m.oHeap+m.ns) by {
      reveal COK();
      assert refOK(b, rfv);
      assert AssignmentCompatible(b, b.fieldModes[n], rfv);

      assert COK(b,  m.oHeap+m.ns);
    }

  } else {
    assert b == rfv;// gulp!

    assert COK(b,  m.oHeap+m.ns) by {
      reveal COK();
      assert refOK(b, rfv);
      assert AssignmentCompatible(b, b.fieldModes[n], rfv);
      assert COK(b,  m.oHeap+m.ns);
    }
    assert COK(rfv,m.oHeap+m.ns);
  }

  assert unchanged(m'.ns - {b});

  assert m'.calid2();
  assert old(m'.calid());

  assert COK(b, m.oHeap+m.ns) &&  COK(rfv,m.oHeap+m.ns);


  //
  assert   (a.fields.Keys - b.fields.Keys) < old(a.fields.Keys - b.fields.Keys) by {
    assert a.fields.Keys == old(a.fields.Keys);
    assert b.fields.Keys == old(b.fields.Keys)+{n};
  }


  assert
    && CallOK(m.m.Values, m.oHeap+m.ns)
    && CallOK(m.ns, m.oHeap+m.ns)
  by {
    assert CallOK(m.m.Values-{b}, m.oHeap+m.ns); //OK
    assert CallOK(m.ns-{b}, m.oHeap+m.ns);

    assert COK(b, m.oHeap+m.ns);
    assert b in  m.oHeap+m.ns by { reveal COK(); }
    CallOKfromCOK(b, m.oHeap+m.ns);
    CallOKWiderFocus(m.ns-{b}, {b}, m.oHeap+m.ns);
  //  assert ((m.ns-{b}) + {b}) == m.ns;   what the FUCK is this doing anyway?

    assert b in m'.m.Values;
    assert b in  m.m.Values;

    assert m.m.Values <= m.oHeap+m.ns by { reveal m.calid(); reveal m.calidOK(); }

    assert COK(b, m.oHeap+m.ns);
    assert b in  m.oHeap+m.ns by { reveal COK(); }
    CallOKfromCOK(b, m.oHeap+m.ns);
    assert CallOK({b}, m.oHeap+m.ns);
    assert CallOK(m.ns-{b}, m.oHeap+m.ns);

    if (b in m.ns) {
      assert b in m.ns;
      assert COK(b, m.oHeap+m.ns);

//      CallOKWiderFocus(m.ns-{b}, {b}, m.oHeap+m.ns);

      reveal COK(), CallOK();
      assert forall o <- (m.ns-{b}) :: COK(o, m.oHeap+m.ns);
      assert forall o <- ({b}) ::  COK(o, m.oHeap+m.ns);
      assert forall o <- ((m.ns-{b})+{b}) :: COK(o, m.oHeap+m.ns);
      assert forall o <- (m.ns) :: COK(o, m.oHeap+m.ns);
      assert CallOK(m.ns, m.oHeap+m.ns);
    } else {
      assert b !in m.ns;
      assert CallOK(m.ns-{b}, m.oHeap+m.ns) by { reveal Call_NOB; }
      assert (m.ns-{b}) == m.ns;
      assert CallOK(m.ns, m.oHeap+m.ns);
    }


    CallOKWiderFocus(m.m.Values-{b}, {b}, m.oHeap+m.ns);
    assert (m.m.Values-{b} + {b}) == m.m.Values;


    assert CallOK(m.m.Values, m.oHeap+m.ns);
    assert CallOK(m.ns, m.oHeap+m.ns);
  }

  //OLDCALID assert m'.calid()g{ reveal MPRIME; }

  assert  m.calidOK()
  by {
    assert old@B4(rm.calidOK());
    reveal m.calidOK();

    assert old@B4(CallOK(m.m.Values, m.oHeap+m.ns));
    assert old@B4(CallOK(m.ns, m.oHeap+m.ns));


    assert rfv in rm.m.Values;
    assert rfv in rm.oHeap+rm.ns;
    assert COK(rfv,m.oHeap+m.ns);

    assert (m.o in  m.oHeap);
    assert (m.m.Keys <= m.oHeap);
    assert (m.m.Values <= m.oHeap+m.ns);
    assert COK(m.o, m.oHeap);
    assert CallOK(m.oHeap);
    assert CallOK(m.m.Keys, m.oHeap);

    assert COK(b,m.oHeap+m.ns);

    // assert CallOK(m.m.Values, m.oHeap+m.ns);
    // assert CallOK(m.ns, m.oHeap+m.ns);
    assert m.calidOK();
  }




  assert unchanged(m'.ns - {b});

// IHasCalidObjects(m);
//
// assert klonVMapOK(m.m);
//
// IHasCalidMap(m);


  // requires AllMapEntriesAreUnique(r.m)
  // requires klonVMapOK(r.m)
  // requires (forall x <- r.m.Keys :: (not(inside(x,r.o)) ==> (r.m[x] == x)))
  // requires (forall x <- r.m.Keys, oo <- x.AMFO :: r.m[oo] in r.m[x].AMFO)

  assert m.calid() by
  {
    reveal m.calid();
    reveal m.calidObjects();
    reveal m.calidOK();
    reveal m.calidMap();
    reveal m.calidSheep();

    assert m.calidObjects();
    assert m.calidOK();


    assert AllMapEntriesAreUnique(m.m);
    assert klonVMapOK(m.m);
    assert (forall x <- m.m.Keys :: (not(inside(x,m.o)) ==> (m.m[x] == x)));
  ///  assert (forall x <- m.m.Keys, oo <- x.AMFO :: m.m[oo] in m.m[x].AMFO); ///KJXFRIDAY13TH


    assert klonAllOwnersAreCompatible(m);
    assert m.readyAll();
    assert allMapOwnersThruKlownOK(m);

    assert m.calidMap();/////////////////////////

    assert m.m.Keys == m.m.Keys;
    reveal m.AreWeNotMen();
    assert forall x <- m.m.Keys :: m.AreWeNotMen(x, m);

    assert (forall x <- m.m.Keys :: m.AreWeNotMen(x, m));
    assert (forall x <- m.m.Keys :: x.fieldModes == m.m[x].fieldModes);
    assert AllMapEntriesAreUnique(m.m);

IHasCalidSheep(m);

    assert m.calidSheep();/////////////////////////

    assert m.calid();

  }
  //
  //   assert m'.calid() by {
  //
  //      reveal MPRIME; reveal m'.calid();
  //
  //      assert old@JUSTBEFORE(m'.calid());
  //      assert m.calid();
  //
  //      assert n !in  old@JUSTBEFORE(b.fields.Keys);
  //
  //      assert old(m'.calid());
  //     }

  assert old(m'.calid());

  MapOKFromCalid(m);
  assert klonVMapOK(m.m);

  print "RETN Clone_Field_Map: ", fmtobj(a), " pivot:", fmtobj(m.o), "\n";


} //end Clone: /_Field_Map


// lemma KERFUCK(k : Object, v : Object, m0 : Klon, m1 : Klon)
// doesn't quite do whta aI thought it did...
//    requires klonCanKV(m0, k, v)
//    requires m1 == klonKV(m0, k, v)
//    requires m0.readyOK(k)
//    ensures  m1.readyOK(k)
//  {}





lemma extendSeq<T>(ss : seq<T>, n : nat)
    requires n < |ss|
    ensures  ss[..n+1] == ss[..n] + [ss[n]]
{}


 lemma extendSeqSet<T>(ss : seq<T>, n : nat)
    requires n < |ss|
    ensures  seq2set(ss[..n+1]) == seq2set(ss[..n]) + seq2set([ss[n]])
{}

 lemma singletonSeqSet<T>(ss : seq<T>, n : nat)
    requires n < |ss|
    ensures  {ss[n]} == seq2set([ ss[n] ])
{}


lemma nqf<T>(a : T, b : T)
    requires a == b
    ensures  {a} == {b} == seq2set([ a ]) == seq2set([ b ])
 {}



// function fielddiff(a : Object, b : Object) : nat
//   reads a, b
//   {| a.fields.Keys - b.fields.Keys |}
//
