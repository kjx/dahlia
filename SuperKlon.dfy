
///have to sort out c_amfx -- make sure it makes sense

function {:axiom} FAKE() : Object

type SuperKlon = m : Klon | wexford2(m)
  witness Klon(map[],
               FAKE(),
               {}, {}, {}, {}, {})
//not sure about this. but...

lemma recBIvsfefBI(f : Object, t : Object)
  requires f.Ready()
  requires t.Ready()
  ensures refBI(f,t) == fefBI(f,t)
{}

lemma recBIvsFLAT(f : Object, t : Object)
  requires f.Ready()
  requires t.Ready()
  ensures (f.AMFB >= t.AMFX) <==> (flatten(f.bound) >= flatten(t.owner))
  ensures refBI(f,t) == fefBI(f,t)
{}

lemma recDIvsFLAT(f : Object, t : Object)
  requires f.Ready()
  requires t.Ready()
  ensures (f.AMFO == t.AMFX) ==> ((flatten(f.ntrnl - {f}) + {f})  == flatten(t.owner))
{}


lemma MoreValidThanValid(o : Object)
  requires o.Ready()
  ensures  o !in o.AMFB
  ensures  o !in o.AMFX
  ensures  o  in o.AMFO
{}

lemma refBI_nesting(a : Object, b : Object, c : Object, m : Klon)
  requires a.Ready()
  requires b.Ready()
  requires c.Ready()

  requires refBI(a,b)

  ensures  (a.AMFO > a.AMFX >= a.AMFB)
  ensures  (b.AMFO > b.AMFX >= b.AMFB)
  ensures  a.AMFB >= b.AMFX
  ensures  (a.AMFO > a.AMFX >= a.AMFB >= b.AMFX >= b.AMFB)
  ensures  a.AMFB >= b.AMFB
{}

lemma refBI_transitive(a : Object, b : Object, c : Object, m : Klon)
  requires a.Ready()
  requires b.Ready()
  requires c.Ready()

  requires refBI(a,b)
  requires refBI(b,c)

  ensures  refBI(a,c)
{}

//
// derived lemmas equality etc
//

lemma {:axiom}  AXIOMAMFOS(a : Object, b : Object)
// equal AMFOs iff same objects
  requires a.Ready()
  requires b.Ready()
  ensures  (a == b)  ==> (a.AMFO == b.AMFO)
  ensures  (a == b) <==  (a.AMFO == b.AMFO)
  ensures  (a == b) <==> (a.AMFO == b.AMFO)



lemma AXIOMAMFO(part : Object, whole : Object)
// o in AMFO ==> o.AMFO <= AMFO
   requires  part.Ready()
   requires  {whole}    <= part.AMFO
   ensures   whole.AMFO <= part.AMFO
   ensures   inside(part,whole)
   {
    AMFOsisAMFOs(part);
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
    AMFOsisAMFOs(part);
   }

//
// inside vs inside
//

lemma fuckenOwnerReady(part : Object, whole : Object)
    requires part.Ready()
    ensures  forall  x <- part.owner :: x.Ready()
    ensures  forall  x <- part.owner :: part.AMFO > x.AMFO
{}

predicate recInside(part : Object, whole : Object) : (r : bool)
    requires part.SKReady()
    decreases part.AMFO
{
//  forall x | x in part.owner ensures (true) { fuckenOwnerReady(x, whole); }

  || (part == whole)
  || (exists x <- part.owner ::
        && (x.SKReady())                ////grr should be unnecessary
        && (part.AMFO > x.AMFO)       ////grr should be unnecessary
        && (recInside(x,whole)))
}

function collectAllOwners(o : Object) : (rv : Owner)
  decreases o.AMFO
  requires  o.SKReady()
{
  o.OvenReadyReady();
  {o} + o.owner + (set xo <- o.owner, co <- collectAllOwners(xo) :: co)
}

lemma collectAllAMFO(o : Object)
  decreases o.AMFO
  requires  o.Ready()
  requires  o.SKReady()
  ensures   o.AMFO == collectAllOwners(o)
  {
      o.OvenReadyReady();
  }

lemma {:isolate_assertions} recInsideCollectsAllOwners1(part : Object, whole : Object)
  decreases part.AMFO
  requires part.SKReady()
  requires recInside(part,whole)
  ensures  (whole in collectAllOwners(part))
{
    part.OvenReadyReady();
}

lemma {:isolate_assertions} recInsideCollectsAllOwners2(part : Object, whole : Object)
  decreases part.AMFO
  requires part.SKReady()
  requires (whole in collectAllOwners(part))
  ensures  recInside(part,whole)
{
    part.OvenReadyReady();
}

lemma recInsideAMFO1(part : Object, whole : Object)
  decreases part.AMFO
  requires part.Ready()
  requires part.SKReady()
////  requires whole.Ready() //why not?

  requires (whole in part.AMFO)
  ensures  recInside(part,whole)
{
      part.OvenReadyReady();
}

lemma recInsideAMFO2(part : Object, whole : Object)
  decreases part.AMFO
  requires part.Ready()
  requires part.SKReady()
//  requires  whole.Ready() //why not?
  requires  recInside(part,whole)
  ensures   (whole in part.AMFO)
{}


lemma InsideRecInside2(part : Object, whole : Object)
   requires part.Ready()
   requires part.SKReady()
   requires whole.Ready() //why not?
   requires    inside(part,whole)
   ensures  recInside(part,whole)
   {
    assert  inside(part,whole);
    assert  part.AMFO >= whole.AMFO;
    AXIOMAMFOREVERSE(part,whole);
    assert whole in part.AMFO;
    collectAllAMFO(part);
    assert (whole in collectAllOwners(part));
    recInsideCollectsAllOwners2(part,whole);
    assert recInside(part,whole);
   }

lemma InsideRecInside1(part : Object, whole : Object)
   requires part.Ready()
   requires part.SKReady()
// requires whole.Ready() //why not?
   requires recInside(part,whole)
   ensures  inside(part,whole)
   {
      recInsideCollectsAllOwners1(part,whole);
      assert (whole in collectAllOwners(part));
      collectAllAMFO(part);
      assert (whole in part.AMFO);
      AXIOMAMFO(part, whole);
   }



lemma AMFOsisAMFOs(o : Object)
   requires o.Ready()
   ensures forall oo <- o.AMFO | oo != o :: (o.AMFO > oo.AMFO)
{}


///////////////////////////////////////////////////////////////////////////////////////////
// the Pointing Lemmas
///////////////////////////////////////////////////////////////////////////////////////////

lemma
INSIDE_CAN_POUNT_OUT(m' : Klon, f : Object, t : Object, o : Object, c : Object)
 requires f.Ready()
 requires o.Ready()
 requires t.Ready()
 requires inside(f,o)
 requires outside(t,o)
 //requires |f.AMFO| == |o.AMFO| + 100   ///arbitrarily deep

 requires refOK(o,t)
 requires f.AMFB >= t.AMFX
 ensures  refOK(f,t)
{
  // assert refOK(o,t);

//   assert (o==t) || refBI(o,t) || refDI(o,t);
//
//   assert (o != t);
//
//   if (refDI(o,t)) {
//       assert {:contradiction} o.AMFO == t.AMFX;
//       assert {:contradiction} t.AMFO == (t.AMFX + {t});
//       assert {:contradiction} t.AMFO > o.AMFO;
//       assert {:contradiction} inside(t,o);
//       assert {:contradiction} false;
//       return;
//   }

  // assert refBI(o,t); //only remaining case
  // assert o.AMFB >= t.AMFX;
  // assert f.AMFB >= t.AMFX;

  // assert refOK(f,t);
}

lemma
 MOVING_ON_IN(m' : Klon, f : Object, t : Object, o : Object, c : Object)
/// can move an object down; doesn't lose access
 requires f.Ready()
 requires o.Ready()
 requires t.Ready()
 requires inside(c,o) && (c != o)
 requires inside(f,c) && (f != c)
 requires |f.AMFO| == |o.AMFO| + 100
 requires refOK(o,t)
 requires outside(t,o)
 requires f.AMFB >= t.AMFX

 ensures refOK(f,t)
{}

lemma outsideAINTEQUALS(a : Object, b : Object)
  requires outside(a,b)
  ensures  a != b
  {}


lemma InsideOutsideAINTEQUALS(a : Object, b : Object, o : Object)
  requires a.Ready()
  requires b.Ready()
  requires o.Ready()
  requires inside(a,o)
  requires outside(b,o)
  ensures  a != b
  {}

lemma NO_INCOMING_REFS(f : Object, t : Object, o : Object)
 requires f.Ready()
 requires o.Ready()
 requires t.Ready()
 requires outside(f,o) //&& (f != o) //unnecessary
 requires inside(t,o)  && (t != o) //perhaps, perhaps, perhaps  //ieStrictlyInside

 ensures not( refOK(f,t) )
 ensures f != t
{
}

lemma INCOMING_REFS_OWNER_ONLY(f : Object, t : Object, o : Object)
 requires f.Ready()
 requires o.Ready()
 requires t.Ready()
 requires outside(f,o) //&& (f != o) //unnecessary
 requires inside(t,o)  //&& (t != o) //perhaps, perhaps, perhaps  //ieStrictlyInside
 requires refOK(f,o)
 requires refOK(f,t)
 ensures  t == o
 ensures f != t
{}



function  subklonKV(m' : Klon, k : Object, v : Object) : (m : Klon)
  requires k !in m'.m.Keys
  requires v !in m'.m.Values
{
m'.(m:=m'.m[k:=v])  //l.(m:=l.m[k:=v])
}



lemma {:verify false} KVdexy(m' : Klon, k : Object, v : Object, m : Klon)
//the whole thing!
//this one is on ice, cos we're choppint up the KVscartchmonkey version...
  requires k !in m'.m.Keys
  requires v !in m'.m.Values
  requires m == subklonKV(m',k,v)

  requires k.Ready()
  requires v.Ready()
  requires forall k <- m'.m.Keys :: k.Ready() && m.m[k].Ready()

  requires allmagic2(m')


  requires magic2(k,v,m')
  ensures  allmagic2(m)

  requires dexford4(m')
  // ensures  dexford4(m)

  {


forall i <- m.m.Keys, j <- m.m.Keys
   ensures dexy_NO_builtin(i,j,m.m[i],m.m[j],m)
   {
      var of := i; var ot := j;  var cf := m.m[i]; var ct := m.m[j];
      //original from, original to, clone from, clone to


  if ((of != k) && (ot != k)) { //already in m', so already OK

    kvdNOTKK(m', k, v, of, ot, cf, ct, m);

        // assert dexy_NO_builtin(i,j,m.m[i],m.m[j],m);
        // assert (refOK(of,ot) ==> refOK(cf,ct));
    } else {
      //at least one of of and ot are k
  if (of == ot) {  //both are!

    kvdEQKK(m', k, v, of, ot, cf, ct, m);

    } else {


    assert of != ot;
    assert (of == k) != (ot == k);
    //from here on, of one of and ot is k, the other is not

  if (refDI(of,ot) && (of == k)) {//refDI(k,ot)

    assert ot != k;
    assert of.AMFO == ot.AMFX;  //by defn DI

  //  kdvDIKN(m', k, v, of, ot, cf, ct, m);

    if (k == v) {
      assert not(of.AMFO >= m.o_amfo); //k outside
      assert of == cf == v == k; //k outside
      // assert refOK(k,v);
      // assert ct == m.m[ot];
      // assert magic(ot,ct,m);

      assert of.AMFO == ot.AMFX;  //ref defin DI
      assert of.AMFO != m.o_amfo;

      assert not(of.AMFO >= m.o_amfo);

      if (ot.AMFX == m.o_amfo) { //directly inside
          assert ((ot != ct) && (ct.AMFX == m.c_amfx));
          assert refOK(of,ot);
          assert refOK(cf,ct);
        } else  {
          assert refOK(cf,ct);
          assert (refOK(of,ot) ==> refOK(cf,ct));
        }

      assert (refOK(of,ot) ==> refOK(cf,ct));

      } else {
        assert ((v != k) && (v.AMFO >= m.c_amfx));  //inside & cloned

        assert (refOK(of,ot) ==> refOK(cf,ct));
      }
        assert refOK(v,ct);
        assert wexy_NO_builtin(i,j,m.m[i],m.m[j],m);
        } else {



      if (refDI(of,k)) {


      if (ot.AMFX == m.o_amfo) { //directly inside
          assert ((ot != ct) && (ct.AMFX == m.c_amfx));
          assert refOK(of,ot);
          assert refOK(cf,ct);

        assume refOK(cf,k);
        }} else {
      if (refBI(of,ot)) {
        assume refOK(cf,ct);
       } else {
        assert not(refOK(of,ot));
        assert dexy_NO_builtin(i,j,m.m[i],m.m[j],m);
       }}}}}


assume dexy_NO_builtin(i,j,m.m[i],m.m[j],m);


   } //end of FORALL statement

// var i := k;  assert (forall j <- m'.m.Keys :: wexy_NO_builtin(i,j,m.m[i],m.m[j],m));
// var j := k;  assert (forall i <- m'.m.Keys :: wexy_NO_builtin(i,j,m.m[i],m.m[j],m));

  assert (forall i <- m.m.Keys, j <- m.m.Keys :: dexy_NO_builtin(i,j,m.m[i],m.m[j],m));

}//done lemma KVdexy




































lemma {:verify false} KVscratchmonkey(m' : Klon, k : Object, v : Object, m : Klon)
//the whole thing!
//current dev version of KVdexy...
//aim is to go through cbopping out cases as sublemmas kvdXXX
  requires k !in m'.m.Keys
  requires v !in m'.m.Values
  requires m == subklonKV(m',k,v)

  requires k.Ready()
  requires v.Ready()
  requires forall k <- m'.m.Keys :: k.Ready() && m.m[k].Ready()

  requires allmagic2(m')


  requires magic2(k,v,m')
//  ensures  allmagic2(m)

  requires dexford4(m')
  // ensures  dexford4(m)
  {


forall i <- m.m.Keys, j <- m.m.Keys
   ensures true
//   ensures dexy_NO_builtin(i,j,m.m[i],m.m[j],m)
   {
      var of := i; var ot := j;  var cf := m.m[i]; var ct := m.m[j];
      //original from, original to, clone from, clone to


  if ((of != k) && (ot != k)) { //already in m', so already OK

    kvdNOTKK(m', k, v, of, ot, cf, ct, m);

        // assert dexy_NO_builtin(i,j,m.m[i],m.m[j],m);
        // assert (refOK(of,ot) ==> refOK(cf,ct));
    } else {
      //at least one of of and ot are k
  if (of == ot) {  //both are!

    kvdEQKK(m', k, v, of, ot, cf, ct, m);

    } else {


    assert of != ot;
    assert (of == k) != (ot == k);
    //from here on, of one of and ot is k, the other is not

  if (refDI(of,ot) && (of == k)) {//refDI(k,ot)

    assert ot != k;
    assert of.AMFO == ot.AMFX;  //by defn DI

//    kdvDIKN(m', k, v, of, ot, cf, ct, m);

    if (k == v) {
      assert not(of.AMFO >= m.o_amfo); //k outside
      assert of == cf == v == k; //k outside
      // assert refOK(k,v);
      // assert ct == m.m[ot];
      // assert magic(ot,ct,m);

      assert of.AMFO == ot.AMFX;  //ref defin DI
      assert of.AMFO != m.o_amfo;

      assert not(of.AMFO >= m.o_amfo);

      if (ot.AMFX == m.o_amfo) { //directly inside
          assert ((ot != ct) && (ct.AMFX == m.c_amfx));
          assert refOK(of,ot);
          assert refOK(cf,ct);
        } else  {
          assert refOK(cf,ct);
          assert (refOK(of,ot) ==> refOK(cf,ct));
        }

      assert (refOK(of,ot) ==> refOK(cf,ct));

      } else {
        assert ((v != k) && (v.AMFO >= m.c_amfx));  //inside & cloned

        assert (refOK(of,ot) ==> refOK(cf,ct));
      }
        assert refOK(v,ct);
        assert wexy_NO_builtin(i,j,m.m[i],m.m[j],m);
                }
//         else {
//
//
//
//       if (refDI(of,k)) {
//
//
//       if (ot.AMFX == m.o_amfo) { //directly inside
//           assert ((ot != ct) && (ct.AMFX == m.c_amfx));
//           assert refOK(of,ot);
//           assert refOK(cf,ct);
//
//         assume refOK(cf,k);
//         }} else {
//       if (refBI(of,ot)) {
//         assume refOK(cf,ct);
//        } else {
//         assert not(refOK(of,ot));
//         assert dexy_NO_builtin(i,j,m.m[i],m.m[j],m);
//        }}}
       }}


assume dexy_NO_builtin(i,j,m.m[i],m.m[j],m);


   } //end of FORALL statement

// var i := k;  assert (forall j <- m'.m.Keys :: wexy_NO_builtin(i,j,m.m[i],m.m[j],m));
// var j := k;  assert (forall i <- m'.m.Keys :: wexy_NO_builtin(i,j,m.m[i],m.m[j],m));

  assume (forall i <- m.m.Keys, j <- m.m.Keys :: dexy_NO_builtin(i,j,m.m[i],m.m[j],m));

} //done lemma KVscratchMonkey











lemma kvdArmedStruggle(m' : Klon, k : Object, v : Object, of : Object, ot : Object, cf : Object, ct: Object, m : Klon)
//refDI(k,ot) case

  requires k !in m'.m.Keys
  requires v !in m'.m.Values
  requires m == subklonKV(m',k,v)

  requires (of != ot)
  requires GRURK: (of != ot)

  requires (refDI(of,ot) && (of == k))

  requires {of, ot} <= m.m.Keys
  requires m.m[of] == cf
  requires m.m[ot] == ct

  requires k.Ready()
  requires v.Ready()
  requires forall k <- m'.m.Keys :: k.Ready() && m.m[k].Ready()

  requires allmagic2(m')
  requires magic2(k,v,m')
//  ensures  allmagic2(m)

  requires dexford4(m')

  // ensures  dexy_NO_builtin(of,ot,cf,ct,m)
  //  ensures  refOK(of,ot) ==> refOK(cf,ct)
  {


//     assert of != ot;
//     assert (of == k) != (ot == k);
//     //from here on, of one of and ot is k, the other is not

//  if (refDI(of,ot) && (of == k)) {//refDI(k,ot)

    assert of != ot by { reveal GRURK; }

    // assert of.AMFO == ot.AMFX;  //by defn DI

  // //  //  kdvDIKN(m', k, v, of, ot, cf, ct, m);

//     if (k == v) {
//       assert not(of.AMFO >= m.o_amfo); //k outside
//       assert of == cf == v == k; //k outside
//       // assert refOK(k,v);
//       // assert ct == m.m[ot];
//       // assert magic(ot,ct,m);
//
//       assert of.AMFO == ot.AMFX;  //ref defin DI
//       assert of.AMFO != m.o_amfo;
//
//       assert not(of.AMFO >= m.o_amfo);
//
//       if (ot.AMFX == m.o_amfo) { //directly inside
//           assert ((ot != ct) && (ct.AMFX == m.c_amfx));
//           assert refOK(of,ot);
//           assert refOK(cf,ct);
//         } else  {
//           assert refOK(cf,ct);
//           assert (refOK(of,ot) ==> refOK(cf,ct));
//         }
//
//       assert (refOK(of,ot) ==> refOK(cf,ct));
      // }
//      else {
//         assert ((v != k) && (v.AMFO >= m.c_amfx));  //inside & cloned
//
//         assert (refOK(of,ot) ==> refOK(cf,ct));
//       }
//         assert refOK(v,ct);
//         assert wexy_NO_builtin(of,ot,cf,ct,m);
                }
//     }
//     }
//
//   }







lemma kvdOTHER(m' : Klon, k : Object, v : Object, of : Object, ot : Object, cf : Object, ct: Object, m : Klon)
//refDI(k,ot) case

  requires k !in m'.m.Keys
  requires v !in m'.m.Values
  requires m == subklonKV(m',k,v)

  requires {of, ot} <= m.m.Keys
  requires m.m[of] == cf
  requires m.m[ot] == ct

  requires k.Ready()
  requires v.Ready()
  requires forall k <- m'.m.Keys :: k.Ready() && m.m[k].Ready()

  requires allmagic2(m')
  requires magic2(k,v,m')
  ensures  allmagic2(m)

  requires dexford4(m')

  // ensures  dexy_NO_builtin(of,ot,cf,ct,m)
  //  ensures  refOK(of,ot) ==> refOK(cf,ct)
  {


  }










lemma {:isolate_assertions}
NOT_ACTUALLY_FUCKED_OUTSIE_CANT_POUNT_IN(m' : Klon, f : Object, t : Object, o : Object, c : Object)
//  requires o in m'.m.Keys
//  requires m'.m[o] == c
//  requires m'.o_amfo == o.AMFO
//  requires m'.c_amfx == c.AMFO

 requires f.Ready()
 requires t.Ready()
 requires o.Ready()
 requires c.Ready()

 requires outside(f,o)
 requires  o != f
 requires inside(t,o)
 requires  t != o
 ensures   f != t

  ensures not(refOK(f,t))
{
  /// AFTER ALL THIS FUCKING WORK
  /// TURNS OUT TO VERIFY WITH... NOTHING.
//   assert f.Ready(); assert t.Ready(); assert o.Ready();
//
//   assert not(f.AMFO >= o.AMFO); //outside(f,o)
//   assert t.AMFO >= o.AMFO; //inside(t,o)
//
//   //  assert f != t;
//   assert not(f.AMFO > o.AMFO);
//   assert t.AMFO >= o.AMFO;
//   assert t != o;
//   AXIOMAMFOS(t,o);
//   assert t.AMFO > o.AMFO;
//   assert f != t;
//
// // assert refDI() case - f.AMFO != t.AMFX
//
// // assume t !in o.AMFO;
//
//
//     assert t.AMFO == (t.AMFX + {t});
//     assert t.AMFO > o.AMFO;
//
//     assert t.AMFX >= o.AMFO;
//
//
//     if (f.AMFO == t.AMFX)
//       {
//         skip();
//
//
//       }
//
//   // assert not(f.AMFO == t.AMFX);
//   // assert not(refDI(f,t));
//
//
//
// //  assert not(refOK(f,t));
// //  assert (f==t) || refBI(f,t) || refDI(f,t);
//
// // assert not(f == t);
// // assert t.AMFO >= o.AMFO;
// // AXIOMAMFOS(f,t);
// // AXIOMAMFOS(f,o);
// // AXIOMAMFOS(t,o);
}





lemma {:isolate_assertions} kvdNOTKK(m' : Klon, k : Object, v : Object, of : Object, ot : Object, cf : Object, ct: Object, m : Klon)

  requires ((of != k) && (ot != k))

  requires k !in m'.m.Keys
  requires v !in m'.m.Values
  requires m == subklonKV(m',k,v)

  requires {of, ot} <= m.m.Keys
  requires m.m[of] == cf
  requires m.m[ot] == ct

  requires k.Ready()
  requires v.Ready()
  requires forall k <- m'.m.Keys :: k.Ready() && m.m[k].Ready()

  requires allmagic2(m')
  requires magic2(k,v,m')
  ensures  allmagic2(m)

  requires dexford4(m')
//  ensures  dexford4(m)

  ensures  dexy_NO_builtin(of,ot,cf,ct,m)
  ensures  refOK(of,ot) ==> refOK(cf,ct)
{
  //the following is there, and works, and is slower than nothing
//   assert v == m.m[k];
//   assert forall mm <- m'.m.Keys :: m'.m[mm]  == m.m[mm];
//   assert forall mm <- m.m.Keys :: ((mm in m'.m.Keys) ==> (m'.m[mm] == m.m[mm]));
//   assert m.m.Keys == m'.m.Keys + {k};
//
//    assert allmagic2(m');
//    assert forall mm <- m'.m.Keys       :: magic2(mm, m.m[mm], m);
//    assert magic2(k,v,m);
//    assert forall mm <- {k}             :: magic2(mm, m.m[mm], m);
//    assert forall mm <- m'.m.Keys + {k} :: magic2(mm, m.m[mm], m);
//    assert forall mm <- m.m.Keys        :: magic2(mm, m.m[mm], m);
//    assert allmagic2(m);
}


predicate kvdReqs(m' : Klon, k : Object, v : Object, of : Object, ot : Object, cf : Object, ct: Object, m : Klon)
{
  && k !in m'.m.Keys
  && v !in m'.m.Values
  && m == subklonKV(m',k,v)

  && {of, ot} <= m.m.Keys
  && m.m[of] == cf
  && m.m[ot] == ct

  && k.Ready()
  && v.Ready()
  && (forall k <- m'.m.Keys :: k.Ready() && m.m[k].Ready())

  && allmagic2(m')
  && magic2(k,v,m')

  && dexford4(m')
}


lemma kvdEQKK(m' : Klon, k : Object, v : Object, of : Object, ot : Object, cf : Object, ct: Object, m : Klon)

  requires (of == ot == k)

  requires kvdReqs(m',k,v,of,ot,cf,ct,m)

  ensures  allmagic2(m)

  //requires dexford4(m')
//  ensures  dexford4(m)

  ensures refOK(of,ot)
  ensures refOK(cf,ct)

  ensures  dexy_NO_builtin(of,ot,cf,ct,m)
  ensures  refOK(of,ot) ==> refOK(cf,ct)
{}


lemma kvdOO(m' : Klon, k : Object, v : Object, of : Object, ot : Object, cf : Object, ct: Object, m : Klon)

  requires not(of.AMFO >= m'.o_amfo) //needs an o_o so we can write inside...
  requires not(ot.AMFO >= m'.o_amfo) //needs an o_o so we can write inside...

  requires kvdReqs(m',k,v,of,ot,cf,ct,m)

  ensures  allmagic2(m)   //a bit slow

//  ensures  dexford4(m)

  ensures  dexy_NO_builtin(of,ot,cf,ct,m)
  ensures  refOK(of,ot) ==> refOK(cf,ct)
{
   assert cf == of;
   assert ct == ot;
  allmagic2restored(m',k,v,m);
}



lemma {:isolate_assertions}  kvdOI(m' : Klon, k : Object, v : Object, of : Object, ot : Object, cf : Object, ct: Object, m : Klon, o : Object, c : Object)

   requires of.Ready()
   requires  o.Ready()
   requires ot.Ready()

  requires not(of.AMFO >= m'.o_amfo) //needs an o_o so we can write inside...
  requires    (ot.AMFO >= m'.o_amfo) //needs an o_o so we can write inside...

  requires kvdReqs(m',k,v,of,ot,cf,ct,m)

  requires k !in m'.m.Keys
  requires v !in m'.m.Values

  requires o in m'.m.Keys
  requires c == m'.m[o]
  requires o.AMFO == m'.o_amfo
  requires c.AMFO == m'.c_amfx

  requires  o.AMFX == c.AMFX
//wanted ensures  (o.AMFO - {o}) == (c.AMFO - {c})  //doesnt allow clone to be pushed down

//KJX but outside stuff arent update by clone - should this be inside(of, o) ==> (refOK(of,ot) ==> refOK(cf,ct))
//KJX but outside stuff arent update by clone - should this be inside(of, o) ==> (refOK(of,ot) ==> refOK(cf,ct))
//KJX but outside stuff arent update by clone - should this be inside(of, o) ==> (refOK(of,ot) ==> refOK(cf,ct))

//wanted but slows everything down
// ensures  allmagic2(m)


  //wanted but slows everything down
  // ensures  dexy_NO_builtin(of,ot,cf,ct,m)
  // ensures  refOK(of,ot) ==> refOK(cf,ct)
{
   assert of == cf by {
    assert not( of.AMFO >= m'.o_amfo) by { assert   allmagic2(m'); }
    }
   assert of.Ready();
   assert o.Ready();
   assert ot.Ready();
   assert outside(of,o); //&& (f != o) //unnecessary;
   assert inside(ot,o);  //&& (t != o) //perhaps, perhaps, perhaps  //ieStrictlyInside;

if (not(refOK(of,ot))) {
    assert not(refOK(of,ot));
    assert  refOK(of,ot) ==> refOK(cf,ct);
    return;
    }
   assert refOK(of,ot);

    INCOMING_REFS_OWNER_ONLY(of,ot,o);

    assert ot == o;

    assert cf == of;
   assert m.m[ot] == ct;


   assert refOK(of,ct);

   assert ct.AMFO == m.c_amfx;
   allmagic2restored(m',k,v,m);
   assert allmagic2(m);

    assert  dexy_NO_builtin(of,ot,cf,ct,m);
    assert  refOK(of,ot) ==> refOK(cf,ct);
}


lemma kvdIO(m' : Klon, k : Object, v : Object, of : Object, ot : Object, cf : Object, ct: Object, o : Object, c : Object, m : Klon)

  requires    (of.AMFO >= m'.o_amfo) //needs an o_o so we can write inside...
  requires not(ot.AMFO >= m'.o_amfo) //needs an o_o so we can write inside...

  requires kvdReqs(m',k,v,of,ot,cf,ct,m)
/////////////////////////////////////////////////////////////////////////
  requires k !in m'.m.Keys
  requires v !in m'.m.Values

  requires o in m'.m.Keys
  requires c == m'.m[o]
  requires o.AMFO == m'.o_amfo
  requires c.AMFO == m'.c_amfx
  requires cf.AMFB >= of.AMFB

  requires  o.AMFX == c.AMFX
  ensures  (o.AMFO - {o}) == (c.AMFO - {c})  //doesnt allow clone to be pushed down

//KJX but outside stuff arent update by clone - should this be inside(of, o) ==> (refOK(of,ot) ==> refOK(cf,ct))
//KJX but outside stuff arent update by clone - should this be inside(of, o) ==> (refOK(of,ot) ==> refOK(cf,ct))
//KJX but outside stuff arent update by clone - should this be inside(of, o) ==> (refOK(of,ot) ==> refOK(cf,ct))

/////////////////////////////////////////////////////////////////////////
//corret but slow ensures  allmagic2(m)
//
  //  ensures  dexy_NO_builtin(of,ot,cf,ct,m)
  //  ensures  refOK(of,ot) ==> refOK(cf,ct)
{
  assert magic2(k,v,m');
  assert ot == ct;
//
  if (refOK(of,ot)) {
    assert of != ot;
    assert not(refDI(of,ot));
    assert refBI(of,ot);
    assert of.AMFB >= ot.AMFX;

    assert cf.AMFB >= of.AMFB;
    assert ct.AMFX == ot.AMFX;
    assert cf.AMFB >= ct.AMFX;
    assert refBI(cf,ct);
    assert refOK(cf,ct);
  }

   allmagic2restored(m',k,v,m);
}


lemma {:isolate_assertions} kvdII(m' : Klon, k : Object, v : Object, of : Object, ot : Object, cf : Object, ct: Object, m : Klon)

  requires kvdReqs(m',k,v,of,ot,cf,ct,m)

  requires forall k <- m'.m.Keys :: k.owner <= m'.m.Keys   //IN-KLON
  requires forall k <- m'.m.Keys :: k.AMFO  <= m'.m.Keys   //IN-KLON
  requires m'.o_amfo <= m'.m.Keys  //IN-KLON

  requires forall o <- m.m.Keys :: && (o.AMFO <= m.m.Keys) && (o.bound <= m.m.Keys) && (o.owner <= m.m.Keys) && (o.ntrnl <= m.m.Keys) //IN-KLON

  requires k.owner <= m.m.Keys   //IN-KLON
  requires k.AMFO  <= m.m.Keys   //IN-KLON
  requires magic3(k,v,m)

  requires dante(of,m)
  requires dante(ot,m)
  requires dante(cf,m)
  requires dante(ct,m)

  requires allmagic2(m')
  requires allmagic3(m')

  requires    (of.AMFO >= m'.o_amfo) //needs an o_o so we can write inside...
  requires    (ot.AMFO >= m'.o_amfo)
   //this means of & ot are both inside: k will be one or other of them...

  // ensures  allmagic2(m) //working?? but tricky
  // ensures  allmagic3(m)

  requires dexford4(m')
//  ensures  dexford4(m)
//
//   ensures  dexy_NO_builtin(of,ot,cf,ct,m)
//   ensures  refOK(of,ot) ==> refOK(cf,ct)
{
  assert kvdReqs(m',k,v,of,ot,cf,ct,m);

  assert
  && {of, ot} <= m.m.Keys
  && m.m[of] == cf
  && m.m[ot] == ct
  ;

  assert m.from(m');
  assert magic3(k,v,m);

  allmagic2restored(m',k,v,m);
  allmagic3restored(m',k,v,m);


  assert allmagic3(m);

  assert k in m.m.Keys;
  assert v in m.m.Values;
  assert m.m[k] == v;
  assert m.o_amfo <= m.m.Keys;
  assert k.owner <= m.m.Keys;
  assert k.AMFO  <= m.m.Keys;

  assert {k, of, ot} <= m.m.Keys;
  assert {v, cf, ct} <= m.m.Values;

  // assert oxy_NO_builtin(of,ot,cf,ct,m');
  // assert(inside(of,ot) ==> inside(cf,ct));
     if (refOK(of,ot)) {

magic3preservesOwnership(m);

//assert forall i <- m.m.Keys, j <- m.m.Keys ::  (oxy_NO_builtin(i,j,m.m[i],m.m[j],m));
assert forall i <- m.m.Keys, j <- m.m.Keys :: (inside(i,j) ==> inside(m.m[i],m.m[j]));

assert forall i <- m.m.Keys, j <- m.m.Keys :: (inside(i,j) ==> inside(m.m[i],m.m[j]));

assert M3K: magic3(k,v,m);
assert M3F: magic3(of,cf,m);
assert M3T: magic3(ot,ct,m);

  assert
  && {of, ot} <= m.m.Keys
  && m.m[of] == cf
  && m.m[ot] == ct
  ;

fuckenHell3(of,ot,cf,ct,m);



// assert (inside(of,ot) ==> inside(cf,ct));
// //
// //     //continue here!
// //     //continue here!
// //     //continue here!
// //     //continue here!
// // //
// // //         assert (of.AMFO >= m.o_amfo) && (ot.AMFO >= m.o_amfo);
// // //         assert cf.AMFO >= m.c_amfx;
// // //         assert ct.AMFO >= m.c_amfx;
//
//   if (of == ot) {
//     assert refOK(of,ot);
//     assert refOK(cf,ct);
//     return;
//   }
//
//   if (refDI(of,ot)) {
//     assert refOK(of,ot);
//     assert (of.AMFO == ot.AMFX);
//     assert magic3(of,cf,m) by { reveal M3F; }
//     assert tragic3(of,m) == cf.AMFO;
//     assert cf.Ready();
//     assert magic3(ot,ct,m) by { reveal M3T; }
//     assert tragic3(ot,m) == ct.AMFO;
//     assert ct.Ready();
//     assert ct.AMFX == ct.AMFO - {ct};
//
//
//   //  assert refOK(cf,ct);
//     return;
//   }
//
//   if (refBI(of,ot)) {
//     assert refOK(of,ot);
//     assert magic3(of,cf,m) by { reveal M3F; }
//     assert magic3(ot,ct,m) by { reveal M3T; }
//   //  assert refOK(cf,ct);
//     return;
//    }
//
//    assert {:contradiction} not(refOK(of,ot));
//    assert {:contradiction} false;
//
// //
//    }
// //
     }
//////////////////////////////t  assert refOK(of,ot) ==> refOK(cf,ct);
}




lemma {:verify false}  //FUCKED2
kdvDIKN(m' : Klon, k : Object, v : Object, of : Object, ot : Object, cf : Object, ct: Object, m : Klon)

  requires (refDI(of,ot) && (of == k))
  requires refDI(k,ot)

  requires not((of != k) && (ot != k))
  requires not(of == ot)

  requires k !in m'.m.Keys
  requires v !in m'.m.Values
  requires m == subklonKV(m',k,v)

  requires {of, ot} <= m.m.Keys
  requires m.m[of] == cf
  requires m.m[ot] == ct

  requires k.Ready()
  requires v.Ready()
  requires forall k <- m'.m.Keys :: k.Ready() && m.m[k].Ready()

  requires allmagic2(m')
  requires magic2(k,v,m')
  ensures  allmagic2(m)

  requires dexford4(m')

  ensures  dexy_NO_builtin(of,ot,cf,ct,m)
  ensures  refOK(of,ot) ==> refOK(cf,ct)
{
    assert of != ot;
    assert (of == k) != (ot == k);
    assert ot != k;
    assert of.AMFO == ot.AMFX;  //by defn DI

    if (k == v) {
      assert not(of.AMFO >= m.o_amfo); //k outside
      assert of == cf == v == k; //k outside
      // assert refOK(k,v);
      // assert ct == m.m[ot];
      // assert magic(ot,ct,m);

      assert of.AMFO == ot.AMFX;  //ref defin DI
      assert of.AMFO != m.o_amfo;

      assert not(of.AMFO >= m.o_amfo);

      if (ot.AMFX == m.o_amfo) { //directly inside
          assert ((ot != ct) && (ct.AMFX == m.c_amfx));
          assert refOK(of,ot);
          assert refOK(cf,ct);
        } else  {
          assert refOK(cf,ct);
          assert (refOK(of,ot) ==> refOK(cf,ct));
        }

      assert (refOK(of,ot) ==> refOK(cf,ct));

      } else {
        assert ((v != k) && (v.AMFO >= m.c_amfx));  //inside & cloned

        assert (refOK(of,ot) ==> refOK(cf,ct));
      }
        assert refOK(v,ct);
}


























//extrabit#1
//         if (ot.AMFO >= m.o_amfo) //inside
//          { assert ((ot != ct) && (ct.AMFO >= m.c_amfx));
//            assert refOK(of,ot);
//            assert refOK(cf,ct); }



lemma {:verify false} KVwexy(m' : Klon, k : Object, v : Object, m : Klon)
  requires k !in m'.m.Keys
  requires v !in m'.m.Values
  requires m == subklonKV(m',k,v)

  requires allmagic(m')


  requires magic(k,v,m')
  ensures  allmagic(m)

  requires cexford4(m')
  ensures  cexford4(m)
  {

assert (forall i <- m'.m.Keys, j <- m'.m.Keys :: cexy_NO_builtin(i,j,m.m[i],m.m[j],m));
assert m.m.Keys == m'.m.Keys + {k};

assert allmagic(m);

assert m.m[k] == v;
assert magic(k,v,m);


forall i <- m.m.Keys, j <- m.m.Keys
   ensures  wexy_NO_builtin(i,j,m.m[i],m.m[j],m)
   {
     var of := i; var ot := j;  var cf := m.m[i]; var ct := m.m[j];

  if (not(of.AMFO >= m.o_amfo))  //from outside
    {
      if (not(ot.AMFO >= m.o_amfo)) //both outside
       {
        assert (not(of.AMFO >= m.o_amfo)) && (not(ot.AMFO >= m.o_amfo));
        assert of == cf;
        assert ot == ct;
        assert refOK(of,ot) ==> refOK(cf,ct);
        } else {
        // //from outside to inside...
        assert (not(of.AMFO >= m.o_amfo)) && (ot.AMFO >= m.o_amfo);
        assert of == cf;
        assert ct.AMFO >= m.c_amfx;

        if ((of == k) && (ot == k))
          {
            // assert k == of == ot == cf == cf == v;
            // assert of.AMFO == ot.AMFO;
            // assert {:contradiction} not( (not(of.AMFO >= m.o_amfo)) && (ot.AMFO >= m.o_amfo) );
            // assert {:contradiction} not( refOK(of,ot));
            // assert {:contradiction} false;
            assert refOK(of,ot) ==> refOK(cf,ct); //staggering
          }
        else if ((of == k) && (ot != k))
         {
            assert of == cf;
            assert of.AMFO == cf.AMFO;
            assert not(of.AMFO >= m.o_amfo);
            assert ot.AMFO >= m.o_amfo;
            if (ot.AMFO > m.o_amfo) { assert refOK(of,ot); }
            assert ct.AMFO >= m.c_amfx;
            //assert magic(k,v,m);
            assert refOK(of,ot) ==> refOK(cf,ct);
          }
        else if ((of != k) && (ot == k))
         {
            assert of == cf;
            assert magic(k,v,m);
            assert refOK(of,ot) ==> refOK(cf,ct);
        } else {
            assert refOK(of,ot) ==> refOK(cf,ct);
        }

        assert refOK(of,ot) ==> refOK(cf,ct);
        }
    } else {
        assume wexy_NO_builtin(i,j,m.m[i],m.m[j],m);
    }
   }



// var i := k;  assert (forall j <- m'.m.Keys :: wexy_NO_builtin(i,j,m.m[i],m.m[j],m));
//
// var j := k;  assert (forall i <- m'.m.Keys :: wexy_NO_builtin(i,j,m.m[i],m.m[j],m));

  assert (forall i <- m.m.Keys, j <- m.m.Keys :: wexy_NO_builtin(i,j,m.m[i],m.m[j],m));

}//done lemma VERIFY FALSE  KVwexy


// assert (of.AMFO >= m.o_amfo);  //from inside
//
//
//       (if (not(ot.AMFO >= m.o_amfo)) then (
//         //from inside to outside
//         assert (of.AMFO >= m.o_amfo) && (not(ot.AMFO >= m.o_amfo));
//         assert cf.AMFO >= m.c_amfx;
//         assert ot == ct;
//         refOK(of,ot) ==> refOK(cf,ct)
//       ) else (
//         //both inside
//         assert (of.AMFO >= m.o_amfo) && (ot.AMFO >= m.o_amfo);
//         assert cf.AMFO >= m.c_amfx;
//         assert ct.AMFO >= m.c_amfx;
//         refOK(of,ot) ==> refOK(cf,ct)))
//





//
//
// assert
//  forall i <- m.m.Keys, j <- m.m.Keys ::
// //wexynobuiltin
//   (var of := i; var ot := j;  var cf := m.m[i]; var ct := m.m[j];
//
//
//
//   if (not(of.AMFO >= m.o_amfo))
//     then //from outside
//       (if (not(ot.AMFO >= m.o_amfo)) then (
//         //both outside
//         assert (not(of.AMFO >= m.o_amfo)) && (not(ot.AMFO >= m.o_amfo));
//         assert of == cf;
//         assert ot == ct;
//         refOK(of,ot) ==> refOK(cf,ct)
//       ) else (
//         //from outside to inside...
//         assert (not(of.AMFO >= m.o_amfo)) && (ot.AMFO >= m.o_amfo);
//         assert of == cf;
//         assert ct.AMFO >= m.c_amfx;
//         refOK(of,ot) ==> refOK(cf,ct)))
//     else //from inside
//       (if (not(ot.AMFO >= m.o_amfo)) then (
//         //from inside to outside
//         assert (of.AMFO >= m.o_amfo) && (not(ot.AMFO >= m.o_amfo));
//         assert cf.AMFO >= m.c_amfx;
//         assert ot == ct;
//         refOK(of,ot) ==> refOK(cf,ct)
//       ) else (
//         //both inside
//         assert (of.AMFO >= m.o_amfo) && (ot.AMFO >= m.o_amfo);
//         assert cf.AMFO >= m.c_amfx;
//         assert ct.AMFO >= m.c_amfx;
//         refOK(of,ot) ==> refOK(cf,ct)))
//
//
//
//   );
//
//








predicate {:isolate_assertions} oxy_NO_builtin(of : Object, ot : Object, cf : Object, ct: Object, m : Klon) : ( rv : bool )
  requires {of, ot} <= m.m.Keys
  requires m.m[of] == cf
  requires m.m[ot] == ct

  //requires allmagic(m)
  // requires magic2(of,cf,m)
  // requires magic2(ot,ct,m)

//  requires (forall x <- m.m.Keys :: (not(x.AMFO >= m.o_amfo) <==> (m.m[x] == x)))
  //seems not to requires ANY other constraints than this one...
//
//   requires (of != cf) ==> (cf.AMFO >= m.c_amfx)
//   requires (ot != ct) ==> (ct.AMFO >= m.c_amfx)


  ensures rv == (inside(of,ot) ==> inside(cf,ct))
{
(inside(of,ot) ==> inside(cf,ct))
}





















predicate wexy(of : Object, ot : Object, cf : Object, ct: Object, m : SuperKlon) : ( rv : bool )
//note doesnt requrie Valid???
// this Kklon has wexford2()  BUILT IN@!!A
  requires {of, ot} <= m.m.Keys
  requires m.m[of] == cf
  requires m.m[ot] == ct

  requires (forall x <- m.m.Keys :: (not(x.AMFO >= m.o_amfo) <==> (m.m[x] == x)))

  requires (of != cf) ==> (cf.AMFO >= m.c_amfx)
  requires (ot != ct) ==> (ct.AMFO >= m.c_amfx)

  ensures rv == (refOK(of,ot) ==> refOK(cf,ct))
{

  // 25DEC 2024 - starting on the 2x2 version inside/outside of ,ot cases
  //
  if (not(of.AMFO >= m.o_amfo))
    then //from outside
      (if (not(ot.AMFO >= m.o_amfo)) then (
        //both outside
        assert (not(of.AMFO >= m.o_amfo)) && (not(ot.AMFO >= m.o_amfo));
        assert of == cf;
        assert ot == ct;
        refOK(of,ot) ==> refOK(cf,ct)
      ) else (
        //from outside to inside...
        assert (not(of.AMFO >= m.o_amfo)) && (ot.AMFO >= m.o_amfo);
        assert of == cf;
        assert ct.AMFO >= m.c_amfx;
        refOK(of,ot) ==> refOK(cf,ct)))
    else //from inside
      (if (not(ot.AMFO >= m.o_amfo)) then (
        //from inside to outside
        assert (of.AMFO >= m.o_amfo) && (not(ot.AMFO >= m.o_amfo));
        assert cf.AMFO >= m.c_amfx;
        assert ot == ct;
        refOK(of,ot) ==> refOK(cf,ct)
      ) else (
        //both inside
        assert (of.AMFO >= m.o_amfo) && (ot.AMFO >= m.o_amfo);
        assert cf.AMFO >= m.c_amfx;
        assert ct.AMFO >= m.c_amfx;
        refOK(of,ot) ==> refOK(cf,ct)))
}




predicate wexy_NO_builtin(of : Object, ot : Object, cf : Object, ct: Object, m : Klon) : ( rv : bool )

  // requires {of, ot} <= m.m.Keys
  // requires m.m[of] == cf
  // requires m.m[ot] == ct

  //requires allmagic(m)
  requires magic2(of,cf,m)
  requires magic2(ot,ct,m)

//  requires (forall x <- m.m.Keys :: (not(x.AMFO >= m.o_amfo) <==> (m.m[x] == x)))
  //seems not to requires ANY other constraints than this one...
//
//   requires (of != cf) ==> (cf.AMFO >= m.c_amfx)
//   requires (ot != ct) ==> (ct.AMFO >= m.c_amfx)


  ensures rv == (refOK(of,ot) ==> refOK(cf,ct))
{

  // 25DEC 2024 - starting on the 2x2 version inside/outside of ,ot cases
  //
  if (not(of.AMFO >= m.o_amfo))
    then //from outside
      (if (not(ot.AMFO >= m.o_amfo)) then (
        //both outside
        assert (not(of.AMFO >= m.o_amfo)) && (not(ot.AMFO >= m.o_amfo));
        assert of == cf;
        assert ot == ct;
        refOK(of,ot) ==> refOK(cf,ct)
      ) else (
        //from outside to inside...
        assert (not(of.AMFO >= m.o_amfo)) && (ot.AMFO >= m.o_amfo);
        assert of == cf;
        assert ct.AMFO >= m.c_amfx;
        refOK(of,ot) ==> refOK(cf,ct)))
    else //from inside
      (if (not(ot.AMFO >= m.o_amfo)) then (
        //from inside to outside
        assert (of.AMFO >= m.o_amfo) && (not(ot.AMFO >= m.o_amfo));
        assert cf.AMFO >= m.c_amfx;
        assert ot == ct;
        refOK(of,ot) ==> refOK(cf,ct)
      ) else (
        //both inside
        assert (of.AMFO >= m.o_amfo) && (ot.AMFO >= m.o_amfo);
        assert cf.AMFO >= m.c_amfx;
        assert ct.AMFO >= m.c_amfx;
        refOK(of,ot) ==> refOK(cf,ct)))
}




predicate dexy(of : Object, ot : Object, cf : Object, ct: Object, m : SuperKlon) : ( rv : bool )
//  requires wexford3(m)
/// HMM doesit still work?
// agan doesn't need Valid??
// this Kklon has wexford2()  BUILT IN !!A
  // requires {of, ot} <= m.m.Keys
  // requires m.m[of] == cf
  // requires m.m[ot] == ct

  // requires (forall x <- m.m.Keys :: (not(x.AMFO >= m.o_amfo) <==> (m.m[x] == x)))

  ensures rv == (refOK(of,ot) ==> refOK(cf,ct))
{

  // 25DEC 2024 - version done by case analysis of the refOK(of,ot)
  //

  if (of == ot) then (
    assert refOK(of,ot);
    refOK(cf,ct)) else (
  if (refDI(of,ot)) then (
    assert refOK(of,ot);
    refOK(cf,ct)) else (
  if (refBI(of,ot)) then (
    assert refOK(of,ot);
    refOK(cf,ct)
  ) else (
    assert not(refOK(of,ot));
    true)))
}



predicate dexy_NO_builtin(of : Object, ot : Object, cf : Object, ct: Object, m : Klon) : ( rv : bool )
//no builtin constraints version
  // requires {of, ot} <= m.m.Keys
  // requires m.m[of] == cf
  // requires m.m[ot] == ct

  // requires (forall x <- m.m.Keys :: (not(x.AMFO >= m.o_amfo) <==> (m.m[x] == x)))

  ensures rv == (refOK(of,ot) ==> refOK(cf,ct))
{

  // 25DEC 2024 - version done by case analysis of the refOK(of,ot)
  //

  if (of == ot) then (
    assert refOK(of,ot);
    refOK(cf,ct)) else (
  if (refDI(of,ot)) then (
    assert refOK(of,ot);
    refOK(cf,ct)) else (
  if (refBI(of,ot)) then (
    assert refOK(of,ot);
    refOK(cf,ct)
  ) else (
    assert not(refOK(of,ot));
    true)))
}



lemma compare_NO_builtin(of : Object, ot : Object, cf : Object, ct: Object, m : Klon)

  requires allmagic2(m)

  requires {of, ot} <= m.m.Keys
  requires m.m[of] == cf
  requires m.m[ot] == ct

//   requires (forall x <- m.m.Keys :: (not(x.AMFO >= m.o_amfo) <==> (m.m[x] == x)))
//
//   requires (of != cf) ==> (cf.AMFO >= m.c_amfx)
//   requires (ot != ct) ==> (ct.AMFO >= m.c_amfx)

  ensures  dexy_NO_builtin(of,ot,cf,ct,m)  ==> wexy_NO_builtin(of,ot,cf,ct,m)
  ensures  dexy_NO_builtin(of,ot,cf,ct,m) <==  wexy_NO_builtin(of,ot,cf,ct,m)
  ensures  dexy_NO_builtin(of,ot,cf,ct,m) <==> wexy_NO_builtin(of,ot,cf,ct,m)

  ensures  dexy_NO_builtin(of,ot,cf,ct,m)  ==> cexy_NO_builtin(of,ot,cf,ct,m)
  ensures  dexy_NO_builtin(of,ot,cf,ct,m) <==  cexy_NO_builtin(of,ot,cf,ct,m)
  ensures  dexy_NO_builtin(of,ot,cf,ct,m) <==> cexy_NO_builtin(of,ot,cf,ct,m)

  ensures  wexy_NO_builtin(of,ot,cf,ct,m)  ==> cexy_NO_builtin(of,ot,cf,ct,m)
  ensures  wexy_NO_builtin(of,ot,cf,ct,m) <==  cexy_NO_builtin(of,ot,cf,ct,m)
  ensures  dexy_NO_builtin(of,ot,cf,ct,m) <==> cexy_NO_builtin(of,ot,cf,ct,m)

  ensures  dexy_NO_builtin(of,ot,cf,ct,m)
      == cexy_NO_builtin(of,ot,cf,ct,m)
      == wexy_NO_builtin(of,ot,cf,ct,m)

{
//
// assert  dexy_NO_builtin(of,ot,cf,ct,m) <==> wexy_NO_builtin(of,ot,cf,ct,m);
// assert  dexy_NO_builtin(of,ot,cf,ct,m) <==> cexy_NO_builtin(of,ot,cf,ct,m);
// assert  dexy_NO_builtin(of,ot,cf,ct,m) <==> cexy_NO_builtin(of,ot,cf,ct,m);
// assert  dexy_NO_builtin(of,ot,cf,ct,m)
//       == cexy_NO_builtin(of,ot,cf,ct,m)
//       == wexy_NO_builtin(of,ot,cf,ct,m);

}

predicate cexy_NO_builtin(of : Object, ot : Object, cf : Object, ct: Object, m : Klon)
//
//   requires {of, ot} <= m.m.Keys
//   requires m.m[of] == cf
//   requires m.m[ot] == ct

{
   refOK(of,ot) ==> refOK(cf,ct)
}

predicate magic3(k : Object, v : Object, m : Klon) : ( rv : bool )
//see allmagic3 for why k & v must be in m already
  requires k in m.m.Keys
  requires v in m.m.Values
  requires m.m[k] == v
  requires m.o_amfo <= m.m.Keys   //IN-KLON
  requires k.owner <= m.m.Keys   //IN-KLON
  requires k.AMFO  <= m.m.Keys   //IN-KLON
  reads m.oHeap`fields, m.oHeap`fieldModes
  reads m.ns`fields, m.ns`fieldModes
{
  var CXTRA := m.c_amfx - mapThruKlon(m.o_amfo, m);
  var OXTRA := mapThruKlon(m.o_amfo, m) - m.c_amfx;

assert  mapThruKlon(m.o_amfo, m) - OXTRA + CXTRA == m.c_amfx;

///KJX continue from here - needs to be done in parallel for owner & AMFO!
///KJX continue from here - needs to be done in parallel for owner & AMFO!
///KJX continue from here - needs to be done in parallel for owner & AMFO!

  && (v.AMFO == (mapThruKlon(k.AMFO, m) - OXTRA + CXTRA )) //and this one???
}


function  tragic3(k : Object, m : Klon) : Owner
  requires k in m.m.Keys
  // requires v in m.m.Values
  // requires m.m[k] == v
  requires m.o_amfo <= m.m.Keys   //IN-KLON
  requires k.owner <= m.m.Keys   //IN-KLON
  requires k.AMFO  <= m.m.Keys   //IN-KLON
  reads m.oHeap`fields, m.oHeap`fieldModes
  reads m.ns`fields, m.ns`fieldModes
{
  var CXTRA := m.c_amfx - mapThruKlon(m.o_amfo, m);
  var OXTRA := mapThruKlon(m.o_amfo, m) - m.c_amfx;

assert  (mapThruKlon(m.o_amfo, m) - OXTRA + CXTRA) == m.c_amfx;

///KJX continue from here - needs to be done in parallel for owner & AMFO!
///KJX continue from here - needs to be done in parallel for owner & AMFO!
///KJX continue from here - needs to be done in parallel for owner & AMFO!

  (mapThruKlon(k.AMFO, m) - OXTRA + CXTRA ) //and this one??
}



lemma  magic3tragic3(k : Object, v : Object, m : Klon)
  requires k in m.m.Keys
  requires v in m.m.Values
  requires m.m[k] == v
  requires m.o_amfo <= m.m.Keys   //IN-KLON
  requires k.owner <= m.m.Keys   //IN-KLON
  requires k.AMFO  <= m.m.Keys   //IN-KLON
  requires magic3(k,v,m)
  ensures (
    var mTKoA := mapThruKlon(m.o_amfo, m);
    var CXTRA := m.c_amfx - mTKoA;
    var OXTRA := mTKoA - m.c_amfx;
    && ((mTKoA - OXTRA + CXTRA) == m.c_amfx)
    && (v.AMFO == tragic3(k,m))
  )
{
    var mTKoA := mapThruKlon(m.o_amfo, m);
    var CXTRA := m.c_amfx - mTKoA;
    var OXTRA := mTKoA - m.c_amfx;
    assert
      && ((mTKoA - OXTRA + CXTRA) == m.c_amfx)
      && (v.AMFO == tragic3(k,m))
      ;
}

lemma magic3sanity(m : Klon, o : Object, c : Object)
  requires o.AMFO == m.o_amfo
  requires c.AMFO == m.c_amfx
  requires o in m.m.Keys
  requires c in m.m.Values
  requires m.m[o] == c
//see allmagic3 for why k & v must be in m already
  requires forall k <- m.m.Keys :: k.owner <= m.m.Keys   //IN-KLON
  requires forall k <- m.m.Keys :: k.AMFO  <= m.m.Keys   //IN-KLON
  requires allmagic3(m)
  requires m.o_amfo <= m.m.Keys
  requires m.c_amfx == m.m[o].AMFO
  ensures  magic3(o, c, m)
{}


predicate allmagic3(m : Klon)
  requires forall k <- m.m.Keys :: k.owner <= m.m.Keys   //IN-KLON
  requires forall k <- m.m.Keys :: k.AMFO  <= m.m.Keys   //IN-KLON
  requires m.o_amfo <= m.m.Keys   //IN-KLON
{

  forall x <- m.m.Keys :: magic3(x,m.m[x],m)
}

lemma allmagic3restored(m' : Klon, k : Object, v : Object, m : Klon)
  requires k !in m'.m.Keys
  requires v !in m'.m.Values
  requires forall k <- m'.m.Keys :: k.owner <= m'.m.Keys   //IN-KLON
  requires forall k <- m'.m.Keys :: k.AMFO  <= m'.m.Keys   //IN-KLON
  requires m'.o_amfo <= m'.m.Keys   //IN-KLON
  requires allmagic3(m')
  requires m == subklonKV(m',k,v)

  requires k.owner <= m.m.Keys   //IN-KLON
  requires k.AMFO  <= m.m.Keys   //IN-KLON
  requires magic3(k,v,m)

  ensures  allmagic3(m)
{
  assert v == m.m[k];
  assert forall mm <- m'.m.Keys :: m'.m[mm]  == m.m[mm];
  assert forall mm <- m.m.Keys :: ((mm in m'.m.Keys) ==> (m'.m[mm] == m.m[mm]));
  assert m.m.Keys == m'.m.Keys + {k};

   assert allmagic3(m');
   assert forall mm <- m'.m.Keys       :: magic3(mm, m.m[mm], m);
   assert magic3(k,v,m);
   assert forall mm <- {k}             :: magic3(mm, m.m[mm], m);
   assert forall mm <- m'.m.Keys + {k} :: magic3(mm, m.m[mm], m);
   assert forall mm <- m.m.Keys        :: magic3(mm, m.m[mm], m);
   assert allmagic3(m);
}


lemma magic3preservesOwnership(m : Klon)
  requires forall k <- m.m.Keys :: k.owner <= m.m.Keys   //IN-KLON
  requires forall k <- m.m.Keys :: k.AMFO  <= m.m.Keys   //IN-KLON
  requires m.o_amfo <= m.m.Keys
  requires allmagic3(m)
  ensures forall i <- m.m.Keys, j <- m.m.Keys ::  (oxy_NO_builtin(i,j,m.m[i],m.m[j],m))
  {
assert forall i <- m.m.Keys :: magic3(i,m.m[i],m);

forall i <- m.m.Keys, j <- m.m.Keys
  ensures (oxy_NO_builtin(i,j,m.m[i],m.m[j],m))
  {
    if (i == j) { return; }
    if (inside(i,j)) {
        assert i.AMFO >= j.AMFO;
        assert magic3(i,m.m[i], m);
        assert magic3(j,m.m[j], m);
    }
    assert (oxy_NO_builtin(i,j,m.m[i],m.m[j],m));
  }
  }


function supertragic(k : Owner, m : Klon) : Owner
  requires m.o_amfo <= m.m.Keys   //IN-KLON
  requires k <= m.m.Keys
  reads m.oHeap`fields, m.oHeap`fieldModes
  reads m.ns`fields, m.ns`fieldModes
{
  var CXTRA := m.c_amfx - mapThruKlon(m.o_amfo, m);
  var OXTRA := mapThruKlon(m.o_amfo, m) - m.c_amfx;

  (mapThruKlon(k,m) - OXTRA + CXTRA )
}

//or should this take another parameter for v?
predicate tragicallyhip(o : Object, m : Klon)
  requires m.o_amfo <= m.m.Keys   //IN-KLON
  requires m.m.Keys >= o.ntrnl > o.owner >= o.bound
  requires m.m.Keys >= o.AMFO  > o.AMFX  >= o.AMFB
  requires o in m.m.Keys
  reads m.oHeap`fields, m.oHeap`fieldModes
  reads m.ns`fields, m.ns`fieldModes
   reads o
{
  var c := m.m[o];

  && (c.bound == supertragic(o.bound, m))
  && (c.AMFB  == supertragic(o.AMFB , m))
  && (c.owner == supertragic(o.owner, m))
  && (c.AMFX  == supertragic(o.AMFX , m))
  && (c.ntrnl == supertragic(o.ntrnl, m))
  && (c.AMFO  == supertragic(o.AMFO , m))
}

opaque predicate acertainratio(o : Object, m : Klon)
{
  reveal o.Ready();
  && (m.o_amfo <= m.m.Keys)   //IN-KLON
  && (m.m.Keys >= o.ntrnl > o.owner >= o.bound)
  && (m.m.Keys >= o.AMFO  > o.AMFX  >= o.AMFB)
  && (o in m.m.Keys)
  && (o.Ready())
}


opaque predicate allcertainratio(m : Klon)
{
  forall o <- m.m.Keys :: acertainratio(o,m)
}


lemma fked1(o1 : Object, o2 : Object, m : Klon)
  requires m.o_amfo <= m.m.Keys   //IN-KLON

  requires m.m.Keys >= o1.ntrnl > o1.owner >= o1.bound
  requires m.m.Keys >= o1.AMFO  > o1.AMFX  >= o1.AMFB
  requires o1 in m.m.Keys
  requires o1.Ready()

  requires m.m.Keys >= o2.ntrnl > o2.owner >= o2.bound
  requires m.m.Keys >= o2.AMFO  > o2.AMFX  >= o2.AMFB
  requires o2 in m.m.Keys
  requires o2.Ready()

  requires (  o1 == o2   )
  ensures  (  m.m[o1] == m.m[o2]   )
{}


lemma {:isolate_assertions} fked2(o1 : Object, o2 : Object, m : Klon)
  requires m.o_amfo <= m.m.Keys   //IN-KLON
  requires o1 in m.m.Keys
  requires o2 in m.m.Keys
  requires acrm: allcertainratio(m)
  requires allcertainratio(m)

  requires forall o <- m.m.Keys :: o.Ready()
//   ensures  m.m.Keys >= o1.ntrnl > o1.owner >= o1.bound
//   ensures  m.m.Keys >= o1.AMFO  > o1.AMFX  >= o1.AMFB
//   ensures  o1 in m.m.Keys
//   ensures  o1.Ready()
//
//   ensures  m.m.Keys >= o2.ntrnl > o2.owner >= o2.bound
//   ensures  m.m.Keys >= o2.AMFO  > o2.AMFX  >= o2.AMFB
//   ensures  o2 in m.m.Keys
//  ensures  o2.Ready()

 requires
   reveal allcertainratio(), acertainratio(), o2.Ready();
   forall k <- m.m.Keys :: tragicallyhip(k, m)

//  requires (inside(o1,o2))
//  ensures  (inside(m.m[o1],m.m[o2]))

//  requires (refDI(o1,o2))
//  ensures  (refDI(m.m[o1],m.m[o2]))

//  requires (refBI(o1,o2))
//  ensures  (refBI(m.m[o1],m.m[o2]))

 requires (refOK(o1,o2))
 ensures  (refOK(m.m[o1],m.m[o2]))
{
  assert allcertainratio(m) by { reveal acrm;}
  assert o2 in m.m.Keys;
  assert acertainratio(o2,m) by { reveal acrm, allcertainratio(); }
  assert
    var o := o2;
      && (m.o_amfo <= m.m.Keys)   //IN-KLON
      && (m.m.Keys >= o.ntrnl > o.owner >= o.bound)
      && (m.m.Keys >= o.AMFO  > o.AMFX  >= o.AMFB)
      && (o in m.m.Keys)
      by { reveal acrm, allcertainratio(), acertainratio(); }
   assert o2 in m.m.Keys && o2.Ready() by { reveal acrm, allcertainratio(), acertainratio(), o2.Ready(); }

  assert  (refOK(m.m[o1],m.m[o2]));
}



lemma fuckenHell(k : Object, v : Object, of : Object, ot : Object, cf : Object, ct: Object, m : Klon)
{}

predicate dante(o : Object, m : Klon)
{
  && o.Ready()
  && (o in m.m.Keys)
  && (o.AMFO <= m.m.Keys)
  && (o.bound <= m.m.Keys)
  && (o.owner <= m.m.Keys)
  && (o.ntrnl <= m.m.Keys)
}

lemma {:isolate_assertions}  fuckenHell2(a : Object, b : Object, c : Object, d : Object, aa : Owner, bb : Owner, cc : Owner, dd : Owner, m : Klon)
  requires dante(a,m)
  requires dante(b,m)
  requires dante(c,m)
  requires dante(d,m)

  requires m.o_amfo <= m.m.Keys
  requires aa == tragic3(a, m)
  requires bb == tragic3(b, m)
  requires cc == aa - bb
  requires dd == mapThruKlon(a.AMFO - b.AMFO, m)

  ensures  cc <= dd
{}


lemma {:isolate_assertions} fuckenHell3(a : Object, b : Object, c : Object, d : Object, m : Klon)
  requires dante(a,m)
  requires dante(b,m)
  requires dante(c,m)
  requires dante(d,m)

  requires m.o_amfo <= m.m.Keys
  requires forall o <- m.m.Keys ::
      && (o.AMFO <= m.m.Keys)
      && (o.bound <= m.m.Keys)
      && (o.owner <= m.m.Keys)
      && (o.ntrnl <= m.m.Keys)

  requires allmagic3(m)
//
//   requires b != c
//   requires b != d
//   requires c != d

  requires c == m.m[a]
  requires d == m.m[b]

//WORKS..  (isn'r thjis enough)
// requires inside(b,a)
// ensures  inside(d,c)

//also fuckenj works
// requires a == b  // inside(b,a)
// ensures  c == d  // inside(d,c)

//DOSNT FUCKEN WORK... WHY???
// requires refOK(a,b) // a == b  // inside(b,a)
// ensures  refOK(c,d) // c == d  // inside(d,c)

// //WORKS!!!
// requires refDI(a,b)
// ensures  refDI(c,d)
//
// DOENST FUCKWN WORKS, FUCKER!!
// requires refBI(a,b)
// ensures  refBI(c,d)

//SHOULD WORK NOWWW... WHY???
//requires refOK(a,b) // a == b  // inside(b,a)
// ensures  refOK(c,d) // c == d  // inside(d,c)
{
  // if (  a == b  ) { assert   a == b  ; assert refOK(c,d); return;}
  // if (refDI(a,b)) { assert refDI(c,d); assert refOK(c,d); return;}
  // if (refBI(a,b)) { assert refBI(c,d); assert refOK(c,d); return;}

}
//
//
// predicate magic3old(k : Object, v : Object, m : Klon) : ( rv : bool )
//
//   requires k !in m.m.Keys
//   requires v !in m.m.Values
//
//   //  requires (forall x <- m.m.Keys :: (not(x.AMFO >= m.o_amfo) <==> (m.m[x] == x)))
//
// //  requires (k != v) ==> (v.AMFO >= m.c_amfx)
// {
//   //  && (if (k.AMFO >= m.o_amfo)
//   //       then ((v != k) && (v.AMFO >= m.c_amfx))
//   //       else ((v == k)))
//   //  && ((k.AMFX == m.o_amfo) ==> (v.AMFX == m.c_amfx))
//
//    && ((k !in m.m.Keys) && (v !in m.m.Values))
//
//    && (var satam := subklonKV(m, k, v);
//     forall i <- m.m.Keys, j <- m.m.Keys :: oxy_NO_builtin(i,j,satam.m[i],satam.m[j],satam))
// }

predicate magic2(k : Object, v : Object, m : Klon) : ( rv : bool )

  //  requires (forall x <- m.m.Keys :: (not(x.AMFO >= m.o_amfo) <==> (m.m[x] == x)))

//  requires (k != v) ==> (v.AMFO >= m.c_amfx)
{
   && (if (k.AMFO >= m.o_amfo)
        then ((v != k) && (v.AMFO >= m.c_amfx))
        else ((v == k)))
   && ((k.AMFX == m.o_amfo) ==> (v.AMFX == m.c_amfx))
}

lemma allmagic2restored(m' : Klon, k : Object, v : Object, m : Klon)
  requires k !in m'.m.Keys
  requires v !in m'.m.Values
  requires allmagic2(m')
  requires magic2(k,v,m')
  requires m == subklonKV(m',k,v)
  ensures  allmagic2(m)
{
  assert v == m.m[k];
  assert forall mm <- m'.m.Keys :: m'.m[mm]  == m.m[mm];
  assert forall mm <- m.m.Keys :: ((mm in m'.m.Keys) ==> (m'.m[mm] == m.m[mm]));
  assert m.m.Keys == m'.m.Keys + {k};

   assert allmagic2(m');
   assert forall mm <- m'.m.Keys       :: magic2(mm, m.m[mm], m);
   assert magic2(k,v,m);
   assert forall mm <- {k}             :: magic2(mm, m.m[mm], m);
   assert forall mm <- m'.m.Keys + {k} :: magic2(mm, m.m[mm], m);
   assert forall mm <- m.m.Keys        :: magic2(mm, m.m[mm], m);
   assert allmagic2(m);
}


predicate magic(k : Object, v : Object, m : Klon) : ( rv : bool )

//  requires (forall x <- m.m.Keys :: (not(x.AMFO >= m.o_amfo) <==> (m.m[x] == x)))

//  requires (k != v) ==> (v.AMFO >= m.c_amfx)
{
      (if (k.AMFO >= m.o_amfo)
        then ((v != k) && (v.AMFO >= m.c_amfx))
        else ((v == k)))
}


predicate allmagic2(m : Klon)
{
  forall x <- m.m.Keys :: magic2(x,m.m[x],m)
}

predicate allmagic(m : Klon)
{
  forall x <- m.m.Keys :: magic(x,m.m[x],m)
}

lemma wexford3allmagic(m : Klon)
  ensures allmagic(m) == wexford3(m)
{}


predicate cexford4(m : Klon)
{
  && (forall i <- m.m.Keys, j <- m.m.Keys :: cexy_NO_builtin(i,j,m.m[i],m.m[j],m))
}


predicate dexford4(m : Klon)
{
  && (forall i <- m.m.Keys, j <- m.m.Keys :: dexy_NO_builtin(i,j,m.m[i],m.m[j],m))
}

predicate wexford4(m : Klon)
  requires allmagic2(m)
{
  && (forall i <- m.m.Keys, j <- m.m.Keys :: wexy_NO_builtin(i,j,m.m[i],m.m[j],m))
}

lemma four4(m : Klon)
  requires allmagic2(m)
  ensures  cexford4(m) == dexford4(m) == wexford4(m)
{}


predicate wexford3(m : Klon)
{
  // && (m.m.Keys   <= m.c)
  // && (m.m.Values <= m.c)


  && (forall x <- m.m.Keys ::
      (if (x.AMFO >= m.o_amfo)
        then ((m.m[x] != x) && (m.m[x].AMFO >= m.c_amfx))
        else ((m.m[x] == x))))

  // && (forall x <- m.m.Keys :: (not(x.AMFO >= m.o_amfo) <==> (m.m[x] == x)))

// && (forall x <- m.m.Keys :: (not(x.AMFO >= m.o_amfo) ==> (m.m[x] == x)))

//  && (forall i <- m.m.Keys, j <- m.m.Keys :: wexy(i,j,m.m[i],m.m[j],m))

}


predicate wexford2(m : Klon)
// note this is built into the SuperKlon
{
  // && (m.m.Keys   <= m.c)
  // && (m.m.Values <= m.c)
  && (forall x <- m.m.Keys :: (not(x.AMFO >= m.o_amfo) ==> (m.m[x] == x)))
  && (forall i <- m.m.Keys, j <- m.m.Keys :: refOK(i,j) ==> refOK(m.m[i],m.m[j]))
}


predicate wexford(m : Klon)
{ forall i <- m.m.Keys, j <- m.m.Keys :: refOK(i,j) ==> refOK(m.m[i],m.m[j]) }

predicate waterford(m : Klon)
{ forall i <- m.m.Keys, j <- m.m.Keys |  refOK(i,j) ::  refOK(m.m[i],m.m[j]) }

lemma wexwater(m : Klon)
  ensures wexford(m) == waterford(m)
{}


//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]





//
// function AllMyConcievableOwners(a : Object) : Owner
//   decreases a.AMFO
//   requires a.Ready()
//   {
//     assert a.Ready();
//     assert forall o <- a.owner ::
//       && a.AMFO > o.AMFO
//       && o.Ready();
//     assert forall oo <- a.owner :: oo.AMFO < a.AMFO;
//     assert forall oo <- a.owner :: oo.Ready();
//     set oo <- a.AMFX, ooo <- AllMyConcievableOwners(oo) :: ooo
//   }



lemma ASetLessThan(a : Object, aa : set<Object>,  bb : set<Object>, cc : set<Object>)
 requires aa != bb
 requires bb != cc
 requires aa != cc

 requires a !in cc

requires aa == bb + {a}
requires aa >= cc

ensures bb >= cc
 {}
