module

public import Formalism.LocalToGlobal.Columns.Bundle0017
public import Formalism.LocalToGlobal.Columns.LevGCount

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.HermitianFormLastCoordinateUniformizerVectorSelf
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : ColRec} {u : D.what₂.Word} (A : CF.AtTTied u) (P : ∀ i hi, CF.LvTied u A i hi)

theorem hx_Pv_max (v : (D.mem u).A.vT) : (A.Pv v).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (A.res v) (A.res_surj v)

def AtTSeen : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ (v : (D.mem u).A.vT) (x : 𝓞 D.host.E) (y : D.what₂.LL),
      D.what₂.embLL y = D.host.emb (D.eTau ((D.fm u).tauOf w v)).1 (x : D.host.E) →
      ((0 : WithTop ℤ) < D.what₂.places.val w y ↔
        x ∈ (if (D.fm u).seenP w then A.Pv v else Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (A.Pv v)))


variable (D u) in
def AtTDisc : Prop :=
  ∀ i, i ≤ D.R.m → ∀ c : (D.mem u).C.cls i,
    Nonempty ((CH.Ld D u i c ⧸ (D.clsLat u i c).comap (CH.Ld D u i c).subtype) ≃ₗ[𝓞 D.host.E]
      (𝓞 D.host.E ⧸ Ideal.span {(((D.mem u).A.T : ℕ) : 𝓞 D.host.E)}))


set_option maxHeartbeats 4000000 in
structure AtTMoves where

  upG : ∀ i v (c : (D.mem u).C.cls i), CH.Ld D u i c → CH.GX D i

  up_tie : ∀ i, i ≤ D.R.m → ∀ v c (y : CH.Ld D u i c), (D.fm u).fv i v c (hxPr A P i v c y) = 1 →
    haveI := (hx_Pv_max A v).isPrime
    Formalism.L2.Herm.SameOff (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (upG i v c y).1 (D.clsLat u i ((D.fm u).up i v c (hxPr A P i v c y)))) (D.clsLat u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (upG i v c y).1 (D.clsLat u i ((D.fm u).up i v c (hxPr A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CH.Ld D u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (upG i v c y).1 (CH.Ld D u i ((D.fm u).up i v c (hxPr A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (CH.Ld D u i c ⊔
          Submodule.span (𝓞 D.host.E) {((D.mem u).A.T : D.host.E)⁻¹ • (y : (D.sp.X i).V)}) ∧
      (∀ (z : CH.Ld D u i ((D.fm u).up i v c (hxPr A P i v c y)))
        (hz : ((D.mem u).A.T : D.host.E) • (upG i v c y).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v _ (hxPr A P i v _ z) = (D.fm u).fv i v c (hxPr A P i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : CH.Ld D u i ((D.fm u).up i v c (hxPr A P i v c y)))
        (hz : (upG i v c y).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v' _ (hxPr A P i v' _ z) = (D.fm u).fv i v' c (hxPr A P i v' c ⟨_, hz⟩))
  dnG : ∀ i v (c : (D.mem u).C.cls i), Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) → CH.GX D i

  dn_tie : ∀ i, i ≤ D.R.m → ∀ v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ≠ 0 →
    haveI := (hx_Pv_max A v).isPrime
    Formalism.L2.Herm.SameOff (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (dnG i v c g).1 (D.clsLat u i ((D.fm u).dn i v c g))) (D.clsLat u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap (dnG i v c g).1 (CH.Ld D u i ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (D.clsLat u i c) ∧
      (∀ (z : CH.Ld D u i ((D.fm u).dn i v c g)) (hz : (dnG i v c g).1 (z : (D.sp.X i).V) ∈ CH.Lk D u (A.Pv v) i c),
        (D.fm u).fv i v _ (hxPr A P i v _ z) = g (hxPrk A P i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : CH.Ld D u i ((D.fm u).dn i v c g)) (hz : (dnG i v c g).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v' _ (hxPr A P i v' _ z) = (D.fm u).fv i v' c (hxPr A P i v' c ⟨_, hz⟩))
  dilG : ∀ i v, ((D.mem u).A.Fv v)ˣ → (D.mem u).C.cls i → CH.GX D i

  dil_tie : ∀ i, i ≤ D.R.m → ∀ v (a : ((D.mem u).A.Fv v)ˣ) c,
      Formalism.HermitianLatticesTheory.gmap (dilG i v a c).1 (D.clsLat u i ((D.fm u).dil i v a c)) = D.clsLat u i c ∧
      (∀ (z : CH.Ld D u i ((D.fm u).dil i v a c)) (hz : (dilG i v a c).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v _ (hxPr A P i v _ z) = (a : (D.mem u).A.Fv v) * (D.fm u).fv i v c (hxPr A P i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : CH.Ld D u i ((D.fm u).dil i v a c)) (hz : (dilG i v a c).1 (z : (D.sp.X i).V) ∈ CH.Ld D u i c),
        (D.fm u).fv i v' _ (hxPr A P i v' _ z) = (D.fm u).fv i v' c (hxPr A P i v' c ⟨_, hz⟩))


set_option maxHeartbeats 4000000 in
structure AtTXp where

  lattice₂ : (D.fm u).clsP → Submodule (𝓞 D.host.E) D.sp.X'.V

  levP : Formalism.L2.Herm.StepLevel0 D.sp.cm D.sp.X' D.host.g (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0)

  clsP : Formalism.L2.Herm.ClassTie D.sp.cm D.sp.X' (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0) levP.U (D.fm u).stabilizer₂ lattice₂

  z0 : (D.sp.X D.R.m).V
  cocycle_zero_mem_invariants : z0 ∈ Submodule.span D.host.E {D.sp.z}
  hermitianForm_lastCoordinateUniformizerVector_self : (D.sp.X D.R.m).hT z0 z0 = ((D.mem u).A.T : D.host.E)
  tilG : (D.fm u).clsP → CH.GX D D.R.m

  til_tie : ∀ c : (D.fm u).clsP,
    Formalism.HermitianLatticesTheory.gmap (tilG c).1 (D.clsLat u D.R.m ((D.fm u).til c)) =
      (lattice₂ c).map (D.sp.iX'.restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0} ∧
    ∀ v (z : CH.Ld D u D.R.m ((D.fm u).til c)) (a : 𝓞 D.host.E),
      (a : D.host.E) = (D.sp.X D.R.m).hT z0 ((tilG c).1 (z : (D.sp.X D.R.m).V)) →
      (D.fm u).fv D.R.m v _ (hxPr A P D.R.m v _ z) = A.res v a


set_option maxHeartbeats 4000000 in
def atTOf (eF : ∀ v : (D.mem u).A.vT, (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (A.eV v).1.asIdeal))
    (hF : ∀ v (a : 𝓞 D.host.F), eF v (A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a)) = Ideal.Quotient.mk _ a)
    (hs : AtTSeen A) (hd : AtTDisc D u) (M : AtTMoves A P) (Xp : AtTXp A P) : CH.AtT D u A.eV eF where
  piU := A.piU
  piU_K := A.piU_K
  piU_norm := A.piU_norm
  piU_cong := A.piU_cong
  Pv := A.Pv
  Pv_max := hx_Pv_max A
  Pv_pi := A.res_pi
  Pv_over := fun v => Ideal.ext fun x => ((A.res_v v x).symm)
  res := A.res
  res_surj := A.res_surj
  res_ker := fun _ => rfl
  res_F := hF
  seen := hs
  disc := hd
  pr := hxPr A P
  pr_surj := hxPr_surj A P
  pr_smul := hxPr_smul A P
  pr_ker := hxPr_ker A P
  fv_ker := hx_fv_ker A P
  prk := hxPrk A P
  prk_surj := hxPrk_surj A P
  prk_smul := hxPrk_smul A P
  prk_ker := hxPrk_ker A P
  te_tie := hx_te A P
  upG := M.upG
  up_tie := M.up_tie
  dnG := M.dnG
  dn_tie := M.dn_tie
  dilG := M.dilG
  dil_tie := M.dil_tie
  lattice₂ := Xp.lattice₂
  levP := Xp.levP
  clsP := Xp.clsP
  z0 := Xp.z0
  cocycle_zero_mem_invariants := Xp.cocycle_zero_mem_invariants
  hermitianForm_lastCoordinateUniformizerVector_self := Xp.hermitianForm_lastCoordinateUniformizerVector_self
  tilG := Xp.tilG
  til_tie := Xp.til_tie

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedGlCore
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV
open Formalism.L2.Forms (kv redM)

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E))
  (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
  (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a))
  (w : Pl E) (hw : ∀ a ∈ w.asIdeal, gloRho v spl halg (oToS F E a) = 0)

theorem gco_red_map {k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hk : k ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :
    ((redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w ⟨k, hk⟩ : GL (Fin n) (kP w)) : Matrix (Fin n) (Fin n) (kP w)).map
        (gloE v spl halg w hw) =
      redM F v ((bc (gloPhi v spl) (bc (prV (E := E) v) k) : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  obtain ⟨y, hy, hr⟩ := St_one_int hk
  ext i j
  rw [Matrix.map_apply, hr w i j, gloE_resS, gloRho_apply]
  have e : ((bc (gloPhi v spl) (bc (prV (E := E) v) k) : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j = gloPhi v spl (prV (E := E) v (y i j : E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [← hy i j]; rfl
  unfold redM
  have hm : ((bc (gloPhi v spl) (bc (prV (E := E) v) k) : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := by
    rw [e]; exact gloPhi_int v spl halg _ (afsplit_prV_int v _ (y i j).2)
  rw [dite_eq_left hm]
  congr 1
  exact Subtype.ext e.symm

variable (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)))

theorem gco_mem_levLoc (w : SG) (hw : ∀ a ∈ w.1.asIdeal, gloRho v spl halg (oToS F E a) = 0) (hov : IsOver v w.1)
    (huniq : ∀ w' : SG, IsOver v w'.1 → w' = w) (hT : v ∉ plUnder F ST)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hx : x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) :
    x ∈ levLoc hc n ST SG (Subgroup.pi Set.univ Hw) v ↔
      ∃ M ∈ Hw w, (M : Matrix (Fin n) (Fin n) (kP w.1)).map (gloE v spl halg w.1 hw) =
        redM F v ((bc (gloPhi v spl) x : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨hJ, hred⟩ := (mem_levU hc n ST SG _).1 hk
    exact ⟨_, hred w (Set.mem_univ w), gco_red_map n v spl halg w.1 hw (congruence_subgroup_le_stabilizer hc n ST hJ)⟩
  · rintro ⟨M, hM, hMx⟩
    have hxU : x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := hx.1
    have hxS : x ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) := by
      rw [← rll_locL_base n ST v hT]; exact hx.2
    have hS := rll_put_mem_St n v hxS
    have hJ : rll_put n v x ∈ J0 hc n ST := by
      refine (mem_mirabolicLevel_iff_reduction hc n ST).2 ⟨rll_put_mem_UAd hc n v hxU, hS, fun P hP => ?_⟩
      rw [rll_put_red n v x hS P (fun h => hT ⟨P, hP, h⟩)]
      exact Subgroup.one_mem _
    refine ⟨rll_put n v x, (mem_levU hc n ST SG _).2 ⟨hJ, ?_⟩, rll_put_self n v x⟩
    intro w' _
    show redAt 1 w'.1 ⟨rll_put n v x, congruence_subgroup_le_stabilizer hc n ST hJ⟩ ∈ Hw w'
    by_cases hw' : IsOver v w'.1
    · obtain rfl := huniq w' hw'
      have h1 := gco_red_map n v spl halg w'.1 hw (congruence_subgroup_le_stabilizer hc n ST hJ)
      rw [rll_put_self, ← hMx] at h1
      have h2 : redAt 1 w'.1 ⟨rll_put n v x, congruence_subgroup_le_stabilizer hc n ST hJ⟩ = M := by
        apply Units.ext
        ext i j
        have := congrFun (congrFun h1 i) j
        rw [Matrix.map_apply, Matrix.map_apply] at this
        exact (gloE v spl halg w'.1 hw).injective this
      rw [h2]; exact hM
    · rw [rll_put_red n v x _ w'.1 hw']
      exact Subgroup.one_mem _


include halg in
theorem gco_fr_lat (hT : v ∉ plUnder F ST) (x : Fin n → v.adicCompletion F) :
    (∃ y ∈ latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseLb E n ST), ∀ b, gloPhi v spl (y b) = x b) ↔
      ∀ b, (((1 : GL (Fin n) (v.adicCompletion F))⁻¹ : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈ v.adicCompletionIntegers F := by
  have hL : latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseLb E n ST) =
      Formalism.UG.stdLat (n := Fin n) (A := E ⊗[F] v.adicCompletion F) (Formalism.BasicNotions.intV E v) :=
    (rll_locL_base n ST v hT).trans (rll_locL_std n v)
  rw [hL, inv_one, Units.val_one, Matrix.one_mulVec]
  constructor
  · rintro ⟨y, hy, hyx⟩ b
    rw [← hyx b]
    exact gloPhi_int v spl halg _ ((afsplit_mem_stdLat _ y).1 hy b)
  · intro hx
    refine ⟨fun b => spl.symm (x b, 0), (afsplit_mem_stdLat _ _).2 fun b => ?_, fun b => ?_⟩
    · refine (Formalism.L2.G.split_integral_completion F E v spl halg _).2 ?_
      rw [RingEquiv.apply_symm_apply]
      exact ⟨hx b, zero_mem _⟩
    · show (spl (spl.symm (x b, 0))).1 = x b
      rw [RingEquiv.apply_symm_apply]

end Core

end Formalism.L2.Col
end
end

