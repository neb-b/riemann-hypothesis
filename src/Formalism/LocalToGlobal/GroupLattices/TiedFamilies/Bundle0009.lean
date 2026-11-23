module

public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0005
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0004
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0008
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieEvR
public import Formalism.LocalToGlobal.GroupLattices.FockModels.Sandwich
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StabilizerCount

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieExC
section
noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)


set_option maxHeartbeats 8000000 in
theorem ptOne_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (u : D.what₂.Word) (hU : SameUloc (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    PtOne ((T u).cls0).lev ((recC D sc Ce Lc I ψ hd).gat u w hg)
      (locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B) :=
  ptOne_rec (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u hU w hg B (frRat_C D sc Ce Lc I ψ hd H0 hL B hB u w hg)
    (hypT_C D sc Ce Lc I ψ hd H0 hL u w hg)


set_option maxHeartbeats 8000000 in
theorem ex_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (u : D.what₂.Word) (hU : SameUloc (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (h1 : EvRatRep (embT (recC D sc Ce Lc I ψ hd)) (recC D sc Ce Lc I ψ hd).what₂.embLL ((recC D sc Ce Lc I ψ hd).gat u w hg)
      (locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg) (embFr (D := recC D sc Ce Lc I ψ hd) T u))
    (h2 : LevelZeroCharacterRational (D := recC D sc Ce Lc I ψ hd) T u) :
    ValEx ((T u).cls0).lev (embT (recC D sc Ce Lc I ψ hd)) (recC D sc Ce Lc I ψ hd).what₂.embLL
      ((recC D sc Ce Lc I ψ hd).gat u w hg) (locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B)
      ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg) (embFr (D := recC D sc Ce Lc I ψ hd) T u) ((T u).cls0).y :=
  ex_rec (D := recC D sc Ce Lc I ψ hd) (X := hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T (gatTiesC D sc Ce Lc I ψ hd)
    (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB) u w hg
    (ptOne_C D sc Ce Lc I ψ hd H0 hL T B hB u hU w hg) h1 h2


set_option maxHeartbeats 8000000 in
theorem ex_C_blk (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (u : D.what₂.Word) (hU : SameUloc (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (h1 : BlockRationalityAtPlace (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) (gatTiesC D sc Ce Lc I ψ hd) u w hg B)
    (h2 : LevelZeroCharacterRational (D := recC D sc Ce Lc I ψ hd) T u) :
    ValEx ((T u).cls0).lev (embT (recC D sc Ce Lc I ψ hd)) (recC D sc Ce Lc I ψ hd).what₂.embLL
      ((recC D sc Ce Lc I ψ hd).gat u w hg) (locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B)
      ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg) (embFr (D := recC D sc Ce Lc I ψ hd) T u) ((T u).cls0).y :=
  ex_C D sc Ce Lc I ψ hd H0 hL T B hBs hB u hU w hg
    (evRatRep_rec (D := recC D sc Ce Lc I ψ hd) (X := hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T
      (gatTiesC D sc Ce Lc I ψ hd) u w hg B h1) h2

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieLatFin
section
noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem htupW_le_htup (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : (D.gat u w hg).P.Tup) :
    (D.gat u w hg).P.HtupW L ≤ (D.gat u w hg).P.Htup L := by
  have hW := Formalism.MainNotions.G.Joints.weylSandwich_of_model D (Formalism.L2.G.Model.modelSandwichG_of_ties D Gt)
  refine Submodule.span_mono ?_
  rintro Z ⟨F, hF, rfl⟩
  refine ⟨F, fun v => ?_, rfl⟩
  refine (Submodule.span_mono ?_ : HtenW (D.gat u w hg).O _ _ ≤ Hten (D.gat u w hg).O _ _) (hF v)
  rintro Y ⟨F', hF', rfl⟩
  exact ⟨F', fun s => (hW u w hg _ _ _).2 (hF' s), rfl⟩

theorem m_le_mna (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : (D.gat u w hg).M ≤ (D.gat u w hg).Mna := by
  intro F hF
  have h1 := (mem_funMod_iff (D.gat u w hg) (D.gat u w hg).P.HtupW F).1 hF
  refine (mem_funMod_iff (D.gat u w hg) (D.gat u w hg).P.Htup F).2 fun i => ?_
  exact ⟨fun L hL => htupW_le_htup Gt u w hg L ((h1 i).1 L hL), (h1 i).2⟩

theorem m_finite_rec (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (h : (D.gat u w hg).FinClasses) :
    Module.Finite (D.gat u w hg).O (D.gat u w hg).M :=
  Formalism.MainNotions.FormalGroupSystem.Pf.m_finite (D.gat u w hg) h (m_le_mna Gt u w hg)

variable {X : Formalism.L2.Herm.Herm0 D} {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : CmpIn D X}

theorem surjRat_rec (H : CmpCore T Gt I) (hG : ∀ u w hg, GatIs D X.lev0 u w hg) (hloc : ValIntRec T Gt I) :
    SurjRat T Gt I :=
  surjRat_pf H hloc (fun u w hg => frac_of_gatIs X.lev0 u w hg (hG u w hg))
    (fun u w hg => m_finite_rec Gt u w hg (finClasses_of_gatIs X.lev0 u w hg (hG u w hg)))

theorem comparison_lattice_span_eq (H : CmpCore T Gt I) (hG : ∀ u w hg, GatIs D X.lev0 u w hg) (hloc : ValIntRec T Gt I)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Submodule.span (D.gat u w hg).O
      (cmpRec T Gt I u w hg '' (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) = (D.gat u w hg).M :=
  latM_rec' H hG hloc (surjRat_rec H hG hloc) u w hg

theorem cmpHyp0P_of_cmpCore (H : CmpCore T Gt I) (hG : ∀ u w hg, GatIs D X.lev0 u w hg) (hloc : ValIntRec T Gt I) :
    CmpHyp0P T Gt I :=
  { ex := H.ex,
    evInj := fun u w hg => evInj_rec Gt I u w hg,
    ptEx := fun u w hg => ptEx_rec X T u w hg I.B,
    ptAll := fun u w hg => ptAll_rec X T u (H.same u) w hg I.B,
    chi := H.chi,
    latM := comparison_lattice_span_eq H hG hloc }

end Formalism.L2.G
end
end

