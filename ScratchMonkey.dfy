

lemma mapThruKlonPointless(o : Object, m : Klon)
  requires o in m.m.Keys
//  requires o.AMFO <= m.m.Keys
  requires m.calid()
  requires m.calidObjects()
  requires m.calidOK()
  requires m.calidMap()
  requires m.calidSheep()
 // requires  (forall k <- m.m.Keys :: k.AMFO <= m.m.Keys)
  requires  (reveal m.calidMap(); (forall k <- m.m.Keys :: mapThruKlon(k.AMFO, m) == m.m[k].AMFO))

  ensures  o.AMFO <= m.m.Keys
  ensures  (set oo <- o.AMFO :: m.m[oo]) == (m.m[o].AMFO)
{
     reveal m.calidMap();

 //  assert (set oo <- o.AMFO :: m.m[oo]) == (m.m[o].AMFO);

}


lemma AMFUCKED(a : Object)
  requires a.Ready()
  requires a.Valid()
  ensures  a.AMFO == flattenAMFOs(a.owner) + {a}
  ensures  a in a.AMFO
  ensures  a.AMFO - {a} == flattenAMFOs(a.owner)
 {}

lemma InTheBox(a : Object, m : Klon)
  requires  COK(a, m.oHeap)
  requires  a.allExternalOwners() <= m.m.Keys
  requires  a.allExternalBounds() <= m.m.Keys
  ensures   COK(a, m.m.Keys+{a})
{
  reveal COK();
assert COK(a, m.oHeap);
assert a.Ready();
assert a.OvenReady();

assert a.AMFX <= m.m.Keys;
assert a.AMFB <= m.m.Keys;
assert a.AMFO == a.AMFX+{a};
assert a.AMFO <= m.m.Keys+{a};
// var context := m.m.Keys+{a};
// assert
//     && (a in context)
//     //&& (a.AMFO <= context)
//     //&& (a.AMFB <= context) //sgould be derivable, AMFB <= AMFO
//     && (a.AMFB <= a.AMFO <= context)
//     && (forall oo <- a.AMFO :: oo.Ready())
//     && (forall o <- (a.AMFO - {a}), ooo <- o.AMFO :: a.AMFO >= o.AMFO > ooo.AMFO)
//   //  && (a.TRUMP()||(a.Ready() && a.Valid()))
//     && (a.Ready())
//     && (a.Valid())
//     && (a.AllOutgoingReferencesAreOwnership(context))
// //    && (a.AllOutgoingReferencesWithinThisHeap(context))
//     && (a.AllOwnersAreWithinThisHeap(context))
//
//     && AllTheseOwnersAreFlatOK(a.AMFO - {a})
//     ;

}
