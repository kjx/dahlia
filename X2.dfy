//Xlone_Via_Map -> Xlone_Xlone_Clone
//Xlone_Xlone_xClone -> Xlone_All_Owners, Object.make(), putInside/putOutside, Xlone_All_Fields
//Xlone_All_Owners -> Xlone_Via_Map
//Xlone_All_Fields -> Xlone_Field_Map
//Xlone_Field_Map ->  Xlone_Via_Map

method Xlone_Via_Map(a : Object, m' : Klon)
  returns (b : Object, m : Klon)
    decreases |m'.oHeap - m'.m.Keys|, |a.AMFO|, |a.fields.Keys|, 20 //Klone_Via_Map

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
    m := m.XXXputOutside(a);
    print "RETN Clone_Via_Map: outside ", fmtobj(a), "\n";
    return; // end outside case
  }

 //start of the Inside case
  b, m := Xlone_Clone_Clone(a, m);
  //end of inside case

  print "RETN Clone_Via_Map: ", fmtobj(a), " pivot:", fmtobj(m.o), "\n";

}//END Xlone_Via_Map






method Xlone_Clone_Clone(a : Object, m' : Klon)
  returns (b : Object, m : Klon)
    decreases |m'.oHeap - m'.m.Keys - {a}|, |a.AMFO|, |a.fields.Keys|, 15
{

  m := m';

  print "CALL Clone_Clone_CLone of:", fmtobj(a), " owned by ", fmtown(a.owner) ,"\n";
  print "VARIANT CCC ", |(m'.oHeap - m'.m.Keys - {a})|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";

  print "Clone_Clone_Clone ", fmtobj(a), " calling CAO", fmtown(a.owner) ,"\n";
  printmapping(m.m);

  var aKeys := a.fields.Keys;

assert ( |m'.oHeap - m'.m.Keys - {a}|, |a.AMFO|, |aKeys|, 15
   decreases to |m.oHeap - m.m.Keys - {a}|, |a.AMFO|, |a.fields.Keys|, 12 );

/////////////////////////////////////////////////////////////////////////////////
  var rm := Xlone_All_Owners(a, m);
/////////////////////////////////////////////////////////////////////////////////

 var rowner := a.owner;
 var rbound := a.bound;

  var rAMXO := flattenAMFOs(rowner);
  var rAMXB := flattenAMFOs(rbound);


  if (a in rm.m.Keys) {

    m := rm;
    b := m.XXXat(a); //HMM

//END FUCKOFF
    print "RETN Clone_Clone_CLone ", fmtobj(a), " already cloned: abandoning ship!!\n";
    return;
  } // a in rm.m.Keys - i.e. randomly done while cloning owners


  print "Clone_Clone_CLone ", fmtobj(a), " have rowner ", fmtown(rowner) ," self not yet cloned\n";

var rrm := rm; //KJX THIS IS EVIL, should clean up and get rid of rrm completel6.


print "Clone_Clone_Clone ", fmtobj(a), " boodle boodle boodle\n";


  var context := rrm.oHeap+rrm.ns;    ///why haul ns in here??? --- cos this the owners for the clone!  - the clowners!


print "CALLING MAKE...";

  b := new Object.XXXmake(a.fieldModes, rowner, rrm.oHeap+rrm.ns, "clone of " + a.nick, rbound);
print "BACK FROM MAKE with ",fmtobj(b),"\n";

assume klonCanKV(rrm, a, b);

      var km := klonKV(rrm,a,b); //there it go4s in!

  //  var km := rrm.(ns := rrm.ns + nu(a,b)).(m:= VMapKV(rrm.m,a,b));

print "go4s: ", |km.m|, " ns: ", |km.ns|,"\n";

var amxo := flattenAMFOs(a.owner);

  //  var xm := rrm.XXXputInside(a,b);
  //  var xm := rrm.putInside(a,b);
      var xm :=  km.XXXputInside(a,b);

  print "Clone_Clone_Clone map updated ", fmtobj(a), ":=", fmtobj(b) ,"\n";

//£££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££

  /////   /////    /////    /////   /////    /////    /////   /////    /////
  /////   /////    /////    /////   /////    /////    /////   /////    /////

//ths is cos our XXXpurInside doesn't compute allattribut3es
//and I can find any US targettedversions...

  assume  xm.o     == m'.o;
  assume  xm.oHeap == m'.oHeap;
  assume  mapLEQ(m'.m,xm.m);
  assume  xm.m.Keys >= m'.m.Keys - {a};

  assume   (m'.oHeap - m'.m.Keys - {a}) >= (xm.oHeap - xm.m.Keys - {a});
  assume   |m'.oHeap - m'.m.Keys - {a}| >= (|xm.oHeap - xm.m.Keys - {a}|);

assume a.fields.Keys == old(a.fields.Keys);

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

//££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££

   m := Xlone_All_Fields(a,b, xm);

  print "RETN Clone_Clone_CLone of ", fmtobj(a), " retuning ", fmtobj(b) ,"\n";

}//end Clone_Clone_Clone


















//$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$






 method Xlone_All_Owners(a : Object,  m' : Klon)  returns (m : Klon)
  decreases |m'.oHeap - m'.m.Keys - {a}|, |a.AMFO|, |a.fields.Keys|, 12

{
  print "CALL Clone_All_Owner of:", fmtobj(a), " owned by ", fmtown(a.owner) ,"\n";
  print "VARIANT CAO ", |m'.oHeap - m'.m.Keys  - {a}|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 12, "\n";
  print "ENTRY   CAO ", a.owner - m'.m.Keys ," a in Keys ", (a !in m'.m.Keys), "\n";

  var rm := m';
  var b : Object;  //do we care..

  var xm := rm;

  var xo : Object;
  var rr : Object;
  var oldmks  : set<Object>;  //dont fucking ask
  var oldmok :=  false;

  var MX := a.owner - xm.m.Keys;

     print "PRELOOP ", |MX|," a in Keys ", (a !in xm.m.Keys), "\n";

  while ((MX != {}) && (a !in xm.m.Keys))

  {

      print "LOOPTOP ", |MX|," a in Keys ", (a !in xm.m.Keys), "\n";

    xo :| xo in MX;

    MX := MX - {xo};

///////////////////////////////////////////////////////////////////

assume (
    |m'.oHeap - m'.m.Keys - {a}|, |a.AMFO|, |old(a.fields.Keys)|, 12
  decreases to
    |xm.oHeap - xm.m.Keys|, |a.AMFO|, |a.fields.Keys|, 20);



/////////////////////////////////////////////////////////////////////

assert (
    |m'.oHeap - m'.m.Keys - {a}|, |a.AMFO|, |old(a.fields.Keys)|, 12
  decreases to
    |xm.oHeap - xm.m.Keys|, |a.AMFO|, |a.fields.Keys|, 20);


    rr, rm := Xlone_Via_Map(xo, xm);


    if (a in rm.m.Keys) {
      m := rm;
      b := m.m[a];

      print "RETN - Clone All Onwers - already clonéd\n";
      return;
    }  // if a is in m.Keys after clone -- if it got added magically...


    MX := MX - rm.m.Keys;

    oldmks := xm.m.Keys;
    oldmok := true;
    xm := rm;
  } // end loop MX

  m := xm;

      print "RETN - Clone All Onwers - done Done DONE\n";

}//END Xlone_All_Owners











////££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££
////££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££


method Xlone_All_Fields(a : Object, b : Object, m' : Klon)
  returns (m : Klon)

  decreases |m'.oHeap - m'.m.Keys - {a}|, |a.AMFO|, fielddiff(a,b), 10

  modifies b`fields
{
  print "CALL Clone_All_Fields: ", fmtobj(a), " pivot:", fmtobj(m'.o), "\n";

  m := m';

//TUESDAY15DEC2024

  print "VARIANT CAF ", |(m.oHeap - m.m.Keys) - {a}|, " ", |a.AMFO|, " ", fielddiff(a,b), " ", 10, "\n";
  print "<<<<<<<<<<<\n";
  print "just cloned ", fmtobj(a), " as ", fmtobj(b), "\n";
  print "<<<<<<<<<<<\n";


  print "<<<<<<<<<<<\n";
  printmapping(m.m);
  print "<<<<<<<<<<<\n";

  var fieldNames : seq<string> := set2seq(a.fields.Keys);


 print "Clone_All_Fields fields:", fmtobj(a), " fields=", fmtseqstr(fieldNames), "\n";


  print "BLOOP BLOOP BLOOP\n";

  for i := 0 to |fieldNames|

  {
    var n : string := fieldNames[i];
    assume n in a.fields.Keys;
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


assume (
    |m'.oHeap - m'.m.Keys - {a}|, |a.AMFO|, old(fielddiff(a,b)), 10
  decreases to
    |m.oHeap - m.m.Keys - {a}|, |a.AMFO|, fielddiff(a,b), 5
 );

    m := Xlone_Field_Map(a,n,b,m);
  }

  print "RETN Clone_All_Fields done ", fmtobj(a), "\n";

  return;
}
//end Xlone_All_Fields

////££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££
////££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££££



method Xlone_Field_Map(a : Object, n : string, b : Object, m' : Klon)
  returns (m : Klon)

  decreases |m'.oHeap - m'.m.Keys - {a}|, |a.AMFO|, fielddiff(a,b), 5 //Xlone_Field_Map

  modifies b`fields
{

  print "CALL Clone_Field_Map ", fmtobj(a), " «", n, "»\n";
  print "VARIANT CFM ", |m'.oHeap - m'.m.Keys - {a}|, " ", |a.AMFO|, " ", fielddiff(a,b), " ", 5, "\n";

  m := m';

  var v_cfm := ((m.oHeap - m.m.Keys + {a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Xlone_Field_Map *vxriant for dxcreases clause*

  var onb := m.ns - {b};
  var ctx := (m.oHeap+m.ns);

  var ofv := XXXCOKat(a,n,m.oHeap);

  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
  var rfv : Object;


assume a in m'.m.Keys;
assume a in m.m.Keys;

assume (
    |m'.oHeap - m'.m.Keys - {a}|, |a.AMFO|, old(fielddiff(a,b)), 15
  decreases to
    |m.oHeap -  m.m.Keys|, |a.AMFO|, |a.fields.Keys|, 20
 );

  rfv, m := Xlone_Via_Map(ofv, m);
  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //

  m.XXXCOKput(b, m.oHeap+m.ns, n, rfv);

  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //

  print "RETN Clone_Field_Map: ", fmtobj(a), " pivot:", fmtobj(m.o), "\n";

} //end Clone_Field_Map
