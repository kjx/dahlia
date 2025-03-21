//Xlone_Via_Map -> Xlone_Xlone_Clone
//Xlone_Xlone_xClone -> Xlone_All_Owners, Object.make(), putInside/putOutside, Xlone_All_Fields
//Xlone_All_Owners -> Xlone_Via_Map
//Xlone_All_Fields -> Xlone_Field_Map
//Xlone_Field_Map ->  Xlone_Via_Map

method Xlone_Via_Map(a : Object, m' : Klon)
  returns (b : Object, m : Klon)
    decreases (m'.oHeap - m'.m.Keys), |a.AMFO|, |a.fields.Keys|, 20 //Klone_Via_Map

  requires m'.calid()
  requires m'.readyAll()
  requires m'.readyOK(a)
  requires allMapOwnersThruKlownOK(m')
  requires COK(a, m'.oHeap) //ties owners into OHEAP but not KLON MAP
  requires klonCanKV(m',a,a)  //hmm, interesting... technically not right but
{
  m := m';

  print "CALL Clone_Via_Map ", fmtobj(a), " m':", m', "\n";

  print "VARIANT CVM ", |(m'.oHeap - m'.m.Keys) - {a}|, " ", |a.AMFO|, " ", |(a.fields.Keys )|, " ", 20, "\n";

  if (a in m.m.Keys){ //already cloned, return
    b := m.m[a];
    print "RETN Clone_Via_Map already cloned ", fmtobj(a),  " m':", m', "\n";
    return;
  }

  if (outside(a,m.o)) { //outside. so just map to itself
    b := a;
    m := m.putOutside(a);
    print "RETN Clone_Via_Map: outside ", fmtobj(a), "\n";
    return; // end outside case
  }

 //start of the Inside case  --- //m'.calid() && COK(a, m'.oHeap)
  b, m := Xlone_Clone_Clone(a, m);
  //end of inside case

  print "RETN Clone_Via_Map: ", fmtobj(a), " pivot:", fmtobj(m.o), "\n";

}//END Xlone_Via_Map



lemma somewhatFUCKED(a : Object)
 requires a.Ready()
 ensures  a.AMFX == flattenAMFOs(a.owner)
 ensures  a.AMFB == flattenAMFOs(a.bound)
{}


method Xlone_Clone_Clone(a : Object, m' : Klon)
  returns (b : Object, m : Klon)
    decreases (m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, |a.fields.Keys|, 15
//this case
  requires IAO: inside(a, m'.o)
  requires ANK: a !in m'.m.Keys

  //all Clone
  requires MCL: m'.calid()
  requires AOH: a in m'.oHeap
  requires COH: COK(a, m'.oHeap)
  requires MRK: m'.readyOK(a)
  requires m'.readyAll()

  //requires COK(a, m'.m.Keys+{a}) //KJXFUCKEDFRIDAY13TH
  //need to establish this at the end of this method I guess...
  //notably if we get here, a had better be in the heap but  NOT in the Klon (yet)
{

assert ((a in m'.oHeap) && (COK(a, m'.oHeap))) by { reveal AOH, COH; }
assert m'.calid() by { reveal MCL; }
assert (inside(a, m'.o)) by { reveal IAO; }
assert (a !in m'.m.Keys) by { reveal ANK; }
assert BNK: m'.boundsNestingOK(a, m'.m.Keys+{a}) by { reveal MRK; assert m'.readyOK(a); m'.boundsNestingFromCalid(a, m'.m.Keys+{a}); }
assert (m'.m.Keys <= m'.oHeap) by { reveal MCL; m'.calidObjectsFromCalid(); }

m := m';
assert m.from(m');
     assert m'.boundsNestingOK(a, m'.m.Keys+{a}) by { reveal BNK; }
assert (a.Ready())  by { assert COK(a, m'.oHeap); RVfromCOK(a, m'.oHeap); assert a.Ready(); }
assert (m.m.Keys <= m.oHeap);
assert m.readyOK(a) by { reveal MRK; }

 assert  a.AMFX == flattenAMFOs(a.owner);
 assert  a.AMFB == flattenAMFOs(a.bound);

  print "CALL Clone_Clone_CLone of:", fmtobj(a), " owned by ", fmtown(a.owner) ,"\n";
  print "VARIANT CCC ", |(m'.oHeap - m'.m.Keys - {a})|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";

  print "Clone_Clone_Clone ", fmtobj(a), " calling CAO", fmtown(a.owner) ,"\n";
  printmapping(m.m);

  var aKeys := a.fields.Keys;

assert ((m'.oHeap - m'.m.Keys), |a.AMFO|, |aKeys|, 15
   decreases to (m.oHeap - m.m.Keys), |a.AMFO|, |a.fields.Keys|, 12);

assert (m.m.Keys <= m.oHeap);
assert m.readyOK(a);
/////////////////////////////////////////////////////////////////////////////////
  var rm := Xlone_All_Owners(a, m);
/////////////////////////////////////////////////////////////////////////////////

assert rm.from(m);

 var rowner := a.owner;
 var rbound := a.bound;

 assert ownerInsideOwner(rowner,rbound) by { reveal MRK; assert m'.readyOK(a); assert a.Ready(); assert a.owner >= a.bound; }

 if (a in rm.m.Keys) {

    m := rm;
    b := m.at(a); //HMM


assert m.from(rm);
//END FUCKOFF
    print "RETN Clone_Clone_CLone ", fmtobj(a), " already cloned: abandoning ship!!\n";


    return;
  } // a in rm.m.Keys - i.e. randomly done while cloning owners


  print "Clone_Clone_CLone ", fmtobj(a), " have rowner ", fmtown(rowner) ," self not yet cloned\n";

var rrm := rm; //KJX THIS IS EVIL, should clean up and get rid of rrm completel6.


print "Clone_Clone_Clone ", fmtobj(a), " boodle boodle boodle\n";


  var context := rrm.oHeap+rrm.ns;    ///why haul ns in here??? --- cos this the owners for the clone!  - the clowners!
     assert m'.boundsNestingOK(a, m'.m.Keys+{a}) by { reveal BNK; }

print "CALLING MAKE...";

  b := new Object.make(a.fieldModes, rowner, rrm.oHeap+rrm.ns, "clone of " + a.nick, rbound);
print "BACK FROM MAKE with ",fmtobj(b),"\n";

assert CHAIN: b.AMFO  > b.AMFX >= b.AMFB == flattenAMFOs(rbound) >= rbound;

assert rrm.from(m');
assert rrm.calid();

//€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€
//€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€
//€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€

assert klonCanKV(rrm, a, b) by {

  var c' := rrm;
  var k  := a;
  var v  := b;

     assert m'.boundsNestingOK(a, m'.m.Keys+{a}) by { reveal BNK; }
     assert m'.boundsNestingOK(k, m'.m.Keys+{k}) by { reveal BNK; }


//klonCanKV unpacked:
  assert klonVMapOK(c'.m) by { KlonVMapOKfromCalid(c'); }
  assert canVMapKV(c'.m, k, v);
  assert (k in c'.oHeap) by { reveal AOH; }
  assert (if (v==k) then (v in c'.oHeap) else (v !in c'.oHeap));
  assert c'.boundsNestingOK(k, c'.oHeap) by { c'.boundsNestingFromCalid(k, c'.oHeap); } //GRRR
  assert c'.boundsNestingOK(v, c'.oHeap+c'.ns+{v})  by { c'.boundsNestingFromCalid(v, c'.oHeap+c'.ns+{v}); }
  assert m'.boundsNestingOK(k, m'.m.Keys+{k}) by { reveal BNK; }
  assert c'.boundsNestingOK(k, c'.m.Keys+{k}) by { reveal BNK;
                                                   assert m'.boundsNestingOK(k, m'.m.Keys+{k});
                                                   m'.boundsNestingWiderContext(k, m'.m.Keys+{k}, c'.m.Keys+{k});
                                                   c'.boundsNestingFromCalid(k, c'.m.Keys+{k});  }
  assert (k.fieldModes == v.fieldModes);
  assert (b.AMFO  > b.AMFX >= b.AMFB >= a.AMFB == flattenAMFOs(rbound) >= rbound) by { reveal CHAIN; }
  assert (v.AMFX >= v.AMFB >= k.AMFB);
}
//€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€
//€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€
//€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€€

assert klonCanKV(rrm, a, b);

    var km := klonKV(rrm,a,b); //there it go4s in!
    var xm := km;

  //  var km := rrm.(ns := rrm.ns + nu(a,b)).(m:= VMapKV(rrm.m,a,b));

print "go4s: ", |km.m|, " ns: ", |km.ns|,"\n";

var amxo := flattenAMFOs(a.owner);

  ////umm this is moved away from
  //  var xm := rrm.YYY(a,b);
  //  var xm := rrm.putInside(a,b);
  //   var xm :=  km.YYYputInside(a,YYY

  print "Clone_Clone_Clone map updated ", fmtobj(a), ":=", fmtobj(b) ,"\n";

//COK(a, mmKeys) can only be establshed there


//££££££££££££££££££££££££££££££££££££££££££££££4£££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££

  /////   /////    /////    /////   /////    /////    /////   /////    /////
  /////   /////    /////    /////   /////    /////    /////   /////    /////

//ths is cos our purInside doesn't compute allattribut3es
//and I can find any US targettedversions...

  assert  xm.o     == m'.o;
  assert  xm.oHeap == m'.oHeap;
  assert  mapLEQ(m'.m,xm.m);
  assert  xm.m.Keys >= m'.m.Keys - {a};

  assert   (m'.oHeap - m'.m.Keys - {a}) >= (xm.oHeap - xm.m.Keys - {a});
  assert   (m'.oHeap - m'.m.Keys + {a}) >= (xm.oHeap - xm.m.Keys + {a});

  assert a.fields.Keys == old(a.fields.Keys);  //unchanged?

var left :=  (m'.oHeap - m'.m.Keys + {a});
var right := (xm.oHeap - xm.m.Keys + {a});

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


//££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££

   m := Xlone_All_Fields(a,b, xm);

  print "RETN Clone_Clone_CLone of ", fmtobj(a), " retuning ", fmtobj(b) ,"\n";

}//end Clone_Clone_Clone
















//$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$






method Xlone_All_Owners(a : Object,  m' : Klon)  returns (m : Klon)
    // clone the ownes of A...
  decreases (m'.oHeap - m'.m.Keys), |a.AMFO|, |a.fields.Keys|, 12

  requires m'.calid()
  requires m'.m.Keys <= m'.oHeap   //calid via calidObjects...
  requires m'.readyAll()
  requires m'.readyOK(a)

  requires a in m'.oHeap
  requires a !in m'.m.Keys //mustn't have cloned a yet...
  requires COK(a, m'.oHeap)


//  requires m'.readyAll()
  requires a.Ready()

  ensures  m.from(m')
  ensures  m.calid()

  ensures  m.ownersInKlown(a)

//probably redundant versions
  ensures a.owner <= m.m.Keys
  ensures a.allExternalOwners() <= m.m.Keys
  ensures mapThruKlon(a.allExternalOwners(),m) <= m.m.Values
//end   redundant versions
  modifies {}
{
  print "CALL Clone_All_Owner of:", fmtobj(a), " owned by ", fmtown(a.owner) ,"\n";
  print "VARIANT CAO ", |m'.oHeap - m'.m.Keys  - {a}|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 12, "\n";
  print "ENTRY   CAO ", a.owner - m'.m.Keys ," a in Keys ", (a !in m'.m.Keys), "\n";

  var rm := m';
  assert rm.from(m');
  assert rm.m.Keys <= rm.oHeap;
  assert a in rm.oHeap;
  assert COK(a, rm.oHeap);


  var b : Object;  //do we care..

  var xm := rm;
  assert xm.from(rm);
  assert rm.from(m');
  assert xm.m.Keys <= xm.oHeap;
  assert a in xm.oHeap;
  assert COK(a, xm.oHeap);

  var xo : Object;
  var rr : Object;
  var oldmks  : set<Object>;  //dont fucking ask
  var oldmok :=  false;


  reveal xm.calid(), xm.calidObjects(), xm.calidOK(), xm.calidMap(), xm.calidSheep();

  var MX := a.owner - xm.m.Keys;
  assert a in xm.oHeap;
  assert COK(a, xm.oHeap);
  reveal COK();
  assert a.owner <= xm.oHeap;
  assert MX <= xm.oHeap;

  assert forall x <- MX :: inside(a,x);

    assert MX <= xm.oHeap;
    assert CallOK(xm.oHeap);
    assert MX <= xm.oHeap;


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

    xo :| xo in MX;

    MX := MX - {xo};

assert (
    (m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, |old(a.fields.Keys)|, 12
  decreases to
    (xm.oHeap - xm.m.Keys),        |a.AMFO|, |a.fields.Keys|, 20);

assert xo.Ready();

//    assert xm.readyOK(xo);

    rr, rm := Xlone_Via_Map(xo, xm);

assert rm.from(xm);

    if (a in rm.m.Keys) {
      m := rm;
      b := m.m[a];

assert m.from(rm);  assert m.calid();

      print "RETN - Clone All Onwers - already clonéd\n";

  assert  m.from(m');
  assert  m.ownersInKlown(a);

      return;
    }  // if a is in m.Keys after clone -- if it got added magically...


    MX := MX - rm.m.Keys;

    oldmks := xm.m.Keys;
    oldmok := true;
    xm := rm;
    assert xm.from(rm);
  } // end loop MX

  m := xm;
assert m.from(xm);  assert m.calid();


      print "RETN - Clone All Onwers - done Done DONE\n";

  assert  m.from(m');
  assert  m.ownersInKlown(a);
}//END Xlone_All_Owners











////££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££
////££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££


method Xlone_All_Fields(a : Object, b : Object, m' : Klon)
  returns (m : Klon)

  decreases (m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, fielddiff(a,b), 10

  requires m'.calid()
  requires m'.readyAll()
  requires m'.readyOK(a)
  requires m'.readyOK(a)
  requires allMapOwnersThruKlownOK(m')
  requires COK(a, m'.oHeap)  //GRRR need to resolve WRT readyOK() and Valid()
  requires klonCanKV(m',a,a)

  requires m'.m.Keys <= m'.oHeap
  requires b.fields.Keys == {}
  requires b in m'.m.Values
  requires b in m'.ns
  requires a.fieldModes == b.fieldModes

  modifies b`fields
{
  print "CALL Clone_All_Fields: ", fmtobj(a), " pivot:", fmtobj(m'.o), "\n";

  m := m';
  assert m.from(m');
  assert m == m';
  assert m.m.Keys >= m'.m.Keys;
  assert m.m.Values >= m'.m.Values;
  assert m.oHeap >= m'.oHeap;
  assert m.oHeap >= m.m.Keys;

  assert m.o == m'.o;
  assert m.oHeap == m'.oHeap;
  assert m.ns == m'.ns;
  assert m.m.Values == m'.m.Values;

  assert a.fieldModes == b.fieldModes;
  assert b in m.ns;
  assert b in m.m.Values;


  assert m.calid();
  assert m.readyAll();
  assert m.readyOK(a);
  assert allMapOwnersThruKlownOK(m');

  assert COK(a, m'.oHeap);
  assert klonCanKV(m',a,a);


  assert a.Valid() by { reveal COK(); assert COK(a, m'.oHeap); }
  assert a.AllFieldsAreDeclared() by { reveal a.Valid();  assert a.Valid(); }
  assert a.fields.Keys <= a.fieldModes.Keys;
  assert a.fields.Keys <= b.fieldModes.Keys;

//TUESDAY15DEC2024

  print "VARIANT CAF ", |(m.oHeap - m.m.Keys) - {a}|, " ", |a.AMFO|, " ", fielddiff(a,b), " ", 10, "\n";
  print "<<<<<<<<<<<\n";
  print "just cloned ", fmtobj(a), " as ", fmtobj(b), "\n";
  print "<<<<<<<<<<<\n";


  print "<<<<<<<<<<<\n";
  printmapping(m.m);
  print "<<<<<<<<<<<\n";

  var fieldNames : seq<string> := set2seq(a.fields.Keys);
  assert forall n <- fieldNames :: n in a.fields.Keys;

  assert forall k <- a.fields.Keys :: (multiset(a.fields.Keys))[k] == 1;
  assert forall s <- fieldNames :: (multiset(fieldNames))[s] == 1;
  assert forall i | 0 <= i < |fieldNames|, j | 0 <= j < |fieldNames| :: (fieldNames[i] == fieldNames[j]) <==> i == j;
  assert b.fields.Keys == {};
  assert b.fields.Keys == seq2set(fieldNames[..0]);

  print "Clone_All_Fields fields:", fmtobj(a), " fields=", fmtseqstr(fieldNames), "\n";

  print "BLOOP BLOOP BLOOP\n";

  assert b.fields.Keys == seq2set(fieldNames[..0]) == {};

  assert  m.o        == m'.o;
  assert  m.oHeap    == m'.oHeap;
  assert  m.ns       >= m'.ns;
  assert  m.m.Keys >= m'.m.Keys ;
  assert  m.m.Values >= m'.m.Values;
  assert  m.oHeap    >= m.m.Keys      >= m'.m.Keys;

  assert a.fieldModes == b.fieldModes;
  assert b in m.ns;
  assert b in m.m.Values;

  for i := 0 to |fieldNames|

    invariant m.o        == m'.o
    invariant m.oHeap    == m'.oHeap
    invariant m.ns       >= m'.ns
    invariant m.m.Keys >= m'.m.Keys
    invariant m.m.Values >= m'.m.Values
    invariant m.oHeap    >= m.m.Keys      >= m'.m.Keys

    invariant a.fieldModes        == b.fieldModes
    invariant seq2set(fieldNames) <= a.fieldModes.Keys
    invariant b in m.ns
    invariant b in m.m.Values

    invariant m.calid()
    invariant m.readyAll()
    invariant m.readyOK(a)

    invariant ((m.oHeap - m.m.Keys +{a}) <= (m'.oHeap - m'.m.Keys +{a}))
    invariant ((m.oHeap - m.m.Keys) <= (m'.oHeap - m'.m.Keys))
    invariant b.fields.Keys == seq2set(fieldNames[..i])
    invariant forall i | 0 <= i < |fieldNames|, j | 0 <= j < |fieldNames| :: (fieldNames[i] == fieldNames[j]) <==> i == j
  {
    var n : string := fieldNames[i];
    assert n in a.fields.Keys;
    assert b.fields.Keys == seq2set(fieldNames[..i]);
    var ofv : Object := a.fields[n];

    print "  TLOOP  ",fmtobj(a),".",n," :=", fmtobj(ofv), "\n";
    print "  TLOOP  (recurse on field ",n,")\n";
    print "  TLOOP m:", |m.oHeap - m.m.Keys|, " m':", |m'.oHeap - m'.m.Keys|, "\n";
    print "  TLOOP b.fieldsKeys==", b.fields.Keys, "\n";
    print "  TINV                ", fieldNames[..i], "\n";
    print "  TLOOPINV            ",seq2set(fieldNames[..i]),"\n";

    print "VARIANT*CAF ", |(m.oHeap - m.m.Keys) - {a}|, " ", |a.AMFO|, " ", fielddiff(a,b), " ", 10, "\n";

    var OLDFLDS := b.fields.Keys;

    var v_caf := ((m'.oHeap - m'.m.Keys +{a}), a.AMFO, (a.fields.Keys), 10);
    var v_cfm := ((m.oHeap - m.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Xlone_Field_Map

    print "v_caf ", v_caf, "\n";
    print "v_cfm ", v_cfm, "\n";

    print "okaoka ", (m'.oHeap - m'.m.Keys +{a}) >  (m.oHeap - m.m.Keys +{a}), "\n";
    print "okaoka ", (m'.oHeap - m'.m.Keys +{a}) == (m.oHeap - m.m.Keys +{a}), "\n";

print "WHOOPS-> ", |m'.oHeap - m'.m.Keys +{a}|, " ", |a.AMFO|," ",|a.fields.Keys - b.fields.Keys|," 10\n";
print "->WHOOPS ", |m'.oHeap - m'.m.Keys +{a}|, " ", |a.AMFO|," ",|a.fields.Keys - b.fields.Keys|," 5 \n";

assert m.oHeap  == m'.oHeap;
assert m.m.Keys >= m'.m.Keys;
assert fielddiff(a,b) <= old(fielddiff(a,b));
assert 5 < 10;

 //a.fieldModes == b.fieldModes

assert (
    (m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, old(fielddiff(a,b)), 10
  decreases to
    (m.oHeap -  m.m.Keys  + {a}), |a.AMFO|, fielddiff(a,b), 5
 );

  assert m.calid();
  assert m.readyAll();
  assert m.readyOK(a);
  assert allMapOwnersThruKlownOK(m);

  assert COK(a, m'.oHeap);
  assert klonCanKV(m',a,a);

  assert n  in a.fields.Keys;
  assert n !in b.fields.Keys;

  assert n  in a.fieldModes;
  assert n  in b.fieldModes;
  assert a.fieldModes == b.fieldModes;
  assert b in m.ns;
  assert b in m.m.Values;

    m := Xlone_Field_Map(a,n,b,m);

  assert m.oHeap == m'.oHeap;
  assert b.fields.Keys == seq2set(fieldNames[..i+1]);

  }//end loop

  print "RETN Clone_All_Fields done ", fmtobj(a), "\n";

  return;
}
//end Xlone_All_Fields

////££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££
////££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££



method Xlone_Field_Map(a : Object, n : string, b : Object, m' : Klon) returns (m : Klon)

  decreases (m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, fielddiff(a,b), 5 //Xlone_Field_Map

  requires m'.calid()
  requires m'.readyAll()
  requires m'.readyOK(a)

  requires allMapOwnersThruKlownOK(m')
  requires COK(a, m'.oHeap)
  requires klonCanKV(m',a,a)

  requires n  in a.fields.Keys
  requires n !in b.fields.Keys

  requires n  in a.fieldModes
  requires n  in b.fieldModes
  requires a.fieldModes == b.fieldModes
  requires b in m'.ns
  requires b in m'.m.Values

  ensures  b.fields.Keys == old(b.fields.Keys) + {n}
  ensures  (a.fields.Keys - b.fields.Keys) < old(a.fields.Keys - b.fields.Keys)
  ensures  m.calid()
  ensures  old(m'.calid())
  ensures  m.readyAll()
  ensures  m.readyOK(a)

  ensures  unchanged(a)
  ensures  unchanged(m'.oHeap)
  ensures  unchanged(m'.m.Values - {b})
  ensures  unchanged(m'.m.Keys)
  ensures  unchanged(m'.ns - {b})  //will this work?

  ensures  m.oHeap  == m'.oHeap
  ensures  m.m.Keys >= m'.m.Keys

  ensures m.o        == m'.o
  ensures m.oHeap    == m'.oHeap
  ensures m.ns       >= m'.ns
  ensures m.m.Keys   >= m'.m.Keys
  ensures m.m.Values >= m'.m.Values
  ensures m.oHeap    >= m.m.Keys      >= m'.m.Keys

///////
  // ensures m.calid()
  // ensures m.readyAll()
  // ensures m.readyOK(a)
  // ensures allMapOwnersThruKlownOK(m)
  // ensures COK(a, m.oHeap) //ties owners into OHEAP but not KLON MAP
  // ensures klonCanKV(m,a,a)
//////


  modifies b`fields
{

  print "CALL Clone_Field_Map ", fmtobj(a), " «", n, "»\n";
  print "VARIANT CFM ", |m'.oHeap - m'.m.Keys - {a}|, " ", |a.AMFO|, " ", fielddiff(a,b), " ", 5, "\n";

  m := m';

  assert m.calid();
  assert m.readyAll();
  assert m.readyOK(a);
  assert allMapOwnersThruKlownOK(m);
  assert COK(a, m.oHeap);
  assert klonCanKV(m,a,a);



  var v_cfm := ((m.oHeap - m.m.Keys + {a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Xlone_Field_Map *vxriant for dxcreases clause*

  var onb := m.ns - {b};
  var ctx := (m.oHeap+m.ns);

  var ofv := COKat(a,n,m.oHeap);

  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
  var rfv : Object;


// assert a in m'.m.Keys;
// assert a in m.m.Keys;

assert
    ((m'.oHeap - m'.m.Keys + {a}), |a.AMFO|, old(fielddiff(a,b)), 5
  decreases to
    (m.oHeap -  m.m.Keys), |a.AMFO|, |a.fields.Keys|, 20
 );


  assert m.calid();
  assert m.readyAll();
  assert m.readyOK(a);
  assert allMapOwnersThruKlownOK(m);
  assert COK(a, m.oHeap);
  assert klonCanKV(m,a,a);

  rfv, m := Xlone_Via_Map(ofv, m);

  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //

  label B4:
  m.COKput(b, m.oHeap+m.ns, n, rfv);
  assert b.fields == old@B4(b.fields)[n:=rfv];

  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //

  print "RETN Clone_Field_Map: ", fmtobj(a), " pivot:", fmtobj(m.o), "\n";


//
//   assume  b.fields.Keys == old(b.fields.Keys) + {n};
//   assume  (a.fields.Keys - b.fields.Keys) < old(a.fields.Keys - b.fields.Keys);
//   assume  m.calid();
//   assume  old(m'.calid());
//   assume  m.readyAll();
//   assume  m.readyOK(a);
//   assume  unchanged(a);
//   assume  unchanged(m'.oHeap);
//   assume  unchanged(m'.m.Values - {b});
//   assume  unchanged(m'.m.Keys);
//   assume  unchanged(m'.ns - {b});
//   assume  m.oHeap  == m'.oHeap;
//   assume  m.m.Keys >= m'.m.Keys;
//   assume m.o        == m'.o;
//   assume m.oHeap    == m'.oHeap;
//   assume m.ns       >= m'.ns;
//   assume m.m.Keys   >= m'.m.Keys;
//   assume m.m.Values >= m'.m.Values;
//   assume m.oHeap    >= m.m.Keys      >= m'.m.Keys;

} //end Clone_Field_Map












function fielddiff(a : Object, b : Object) : nat
  reads a, b
  {| a.fields.Keys - b.fields.Keys |}