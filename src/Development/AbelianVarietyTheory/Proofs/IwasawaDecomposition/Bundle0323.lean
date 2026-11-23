module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0315
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0312
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalEqOfClassesRelatedAtPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt.FvOff
open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases


set_option maxHeartbeats 1000000 in
theorem fT_move {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (w : HeightOneSpectrum (𝓞 F)) (hw : (T : 𝓞 F) ∈ w.asIdeal)
    (y y' η κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (hκ : κ ∈ S.U) (hη : bc (prV (E := E) w) η = 1)
    (he : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y' = y * η * κ) (z' : Fin n → E)
    (hx : ((bc (prV (E := E) w) y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) ((γ.1 *ᵥ z') a)) ∈
      latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)))
    (hx' : ((bc (prV (E := E) w) y')⁻¹).1 *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) (z' a)) ∈
      latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) :
    S.fT w hw ⟨_, hx'⟩ = S.fT w hw ⟨_, hx⟩ := by
  have hk : y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y' = η * κ := by
    rw [mul_assoc, he]; group
  have hkw : bc (prV (E := E) w) (y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y') =
      bc (prV (E := E) w) κ := by
    rw [hk, map_mul, hη, one_mul]
  have hm := GlobalTheory.LevelHecke.MovePair.mov_mulVec w y y' γ z'
  rw [hkw] at hm
  have hloc : bc (prV (E := E) w) κ ∈ S.Uloc w := ((S.U_eq κ).1 hκ).2 w
  rw [S.UlocAlt w hw] at hloc
  obtain ⟨hg, hf⟩ := (Subgroup.mem_inf.1 hloc).2
  rw [← hf ⟨_, hx'⟩]
  congr 1
  exact Subtype.ext hm


set_option maxHeartbeats 1000000 in
theorem fT_adStep {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (w w' : HeightOneSpectrum (𝓞 F)) (hw : (T : 𝓞 F) ∈ w'.asIdeal) (hne : w' ≠ w)
    (y y' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (hA : Formalism.L2.Herm.AdStep σ J S.U y y' γ w) (z z' : Fin n → E) (hz : z = γ.1 *ᵥ z')
    (hx : ((bc (prV (E := E) w') y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (w'.adicCompletion F) (z a)) ∈
      latS (F := F) (w'.adicCompletion F) (intV E w') (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)))
    (hx' : ((bc (prV (E := E) w') y')⁻¹).1 *ᵥ (fun a => inclE (F := F) (w'.adicCompletion F) (z' a)) ∈
      latS (F := F) (w'.adicCompletion F) (intV E w') (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) :
    S.fT w' hw ⟨_, hx'⟩ = S.fT w' hw ⟨_, hx⟩ := by
  obtain ⟨κ, hκ, η, -, hη, he⟩ := hA
  subst hz
  exact fT_move S w' hw y y' η κ γ hκ (hη _ hne) he z' hx hx'


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem ld_loc_ch {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
    {cc : cl → (D.mem u).C.cls i}
    (K : LevelChart D (D.mem u).A.T (badG D) i hi stab (fun c => clsCrd D u i hi (cc c)))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (c : cl)
    (x : Fin (D.R.N i) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Ld D u i hi (cc c)) ↔
      ((bc (prV (E := D.host.E) v) (K.y c).1)⁻¹).1 *ᵥ x ∈
        latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
          (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb)) := by
  let φ := (D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm)
  letI : Submodule.IsLattice D.host.E (clsCrd D u i hi (cc c)) := bwB_clsCrd_lat D u i hi (cc c)
  have hL : Submodule.IsFullLattice D.host.E (clsCrd D u i hi (cc c)) := by
    constructor
    change Submodule.span D.host.E (((D.clsLat u i (cc c)).map
      (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) = ⊤
    rw [show Submodule.span D.host.E (((D.clsLat u i (cc c)).map
        (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) =
        (Submodule.span D.host.E (D.clsLat u i (cc c) : Set _)).map φ.toLinearMap by
          rw [Submodule.map_span]; rfl,
      (D.clsLat_lat u i (cc c)).span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact φ.surjective
  letI : Submodule.IsLattice D.host.E K.lev.Lb :=
    Submodule.IsLattice.of_fg D.host.E (Module.Finite.iff_fg.1 K.lev.Lb_fin)
  have hLb : Submodule.IsFullLattice D.host.E K.lev.Lb := ⟨K.lev.Lb_span⟩
  refine GlobalTheory.DualCompletion.dual_move D.host.F D.host.E (sigD D) _ (gramN D i hi) v (clsCrd D u i hi (cc c)) K.lev.Lb
    (bc (prV (E := D.host.E) v) (K.y c).1) (bwB_gramN_det D i hi) hL hLb
    (Formalism.UG.P.afsplit_bc_mem _ _ _ _ (K.y c).2) (fun x => ?_) x
  rw [← map_inv]
  exact rlv_yloc v (K.y c).1 (K.y_lat c) x


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem ld_in {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
    {cc : cl → (D.mem u).C.cls i}
    (K : LevelChart D (D.mem u).A.T (badG D) i hi stab (fun c => clsCrd D u i hi (cc c)))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (c : cl) (z : Fin (D.R.N i) → D.host.E) (hz : z ∈ Ld D u i hi (cc c)) :
      ((bc (prV (E := D.host.E) v) (K.y c).1)⁻¹).1 *ᵥ (fun a => inclE (F := D.host.F) (v.adicCompletion D.host.F) (z a)) ∈
        latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
          (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb)) :=
  (ld_loc_ch K v c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem fv_off_cls {D : D7} {u : D.what₂.Word} {A : AtTTied u} {i : ℕ} {hi : i ≤ D.R.m} (P : LvTied u A i hi)
    (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) (hT : FvTie P K fMe)
    (v v' : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E)
    (hA : Formalism.L2.Herm.AdStep (sigD D) (gramN D i hi) K.lev.U (K.y c).1 (K.y c').1 γ (A.eV v).1) (hv : v' ≠ v)
    (z : Ld D u i hi c) (z' : Ld D u i hi c') (hz : z.1 = γ.1 *ᵥ z'.1) :
    (D.fm u).fv i v' c' (P.pr v' c' z') = (D.fm u).fv i v' c (P.pr v' c z) := by
  have hw : (A.eV v').1 ≠ (A.eV v).1 := fun h => hv (A.eV.injective (Subtype.ext h))
  have hx := ld_in (cc := fun c => c) K.toChart (A.eV v').1 c z.1 z.2
  have hx' := ld_in (cc := fun c => c) K.toChart (A.eV v').1 c' z'.1 z'.2
  have e := fT_adStep K.lev (A.eV v).1 (A.eV v').1 (A.eV v').2 hw (K.y c).1 (K.y c').1 γ hA z.1 z'.1 hz hx hx'
  exact (hT v' c' z' hx').trans ((congrArg (fMe v') e).trans (hT v' c z hx).symm)


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem fv_off_ch {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {Ch : Type} {chOf : (D.mem u).C.cls i → Ch}
    {res : ∀ v, 𝓞 D.host.E →+* (D.mem u).A.Fv v}
    (L : LevelCompatibleLattices (D.fm u) (D.mem u).A.T res i hi (fun c => clsCrd D u i hi c))
    (eV : (D.mem u).A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal})
    (K : ∀ β : Ch, LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1))
    (fMe : ∀ β v, (K β).lev.fM (eV v).1 (eV v).2 ≃+ (D.mem u).A.Fv v) (hT : FvTieG L eV K fMe)
    (v v' : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (hβ : chOf c' = chOf c) (γ : GL (Fin (D.R.N i)) D.host.E)
    (hA : Formalism.L2.Herm.AdStep (sigD D) (gramN D i hi) (K (chOf c)).lev.U ((K (chOf c)).y ⟨c, rfl⟩).1
      ((K (chOf c)).y ⟨c', hβ⟩).1 γ (eV v).1) (hv : v' ≠ v)
    (z : LdG D i hi (clsCrd D u i hi c)) (z' : LdG D i hi (clsCrd D u i hi c')) (hz : z.1 = γ.1 *ᵥ z'.1) :
    (D.fm u).fv i v' c' (L.pr v' c' z') = (D.fm u).fv i v' c (L.pr v' c z) := by
  have hw : (eV v').1 ≠ (eV v).1 := fun h => hv (eV.injective (Subtype.ext h))
  have hx := ld_in (cc := fun c : {c' // chOf c' = chOf c} => c.1) (K (chOf c)) (eV v').1 ⟨c, rfl⟩ z.1 z.2
  have hx' := ld_in (cc := fun c : {c' // chOf c' = chOf c} => c.1) (K (chOf c)) (eV v').1 ⟨c', hβ⟩ z'.1 z'.2
  have e := fT_adStep (K (chOf c)).lev (eV v).1 (eV v').1 (eV v').2 hw _ _ γ hA z.1 z'.1 hz hx hx'
  exact (hT v' (chOf c) ⟨c', hβ⟩ z' hx').trans ((congrArg (fMe (chOf c) v') e).trans (hT v' (chOf c) ⟨c, rfl⟩ z hx).symm)


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem fv_eq_of_adC : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v v' (c c' : ((I.rec7 l Z).mem u).C.cls i) (γ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), AdC (F u) i hi c c' γ ((F u).atT.eV v).1 → v' ≠ v → ∀ (z : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi c) (z' : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi c'), z.1 = γ.1 *ᵥ z'.1 → ((I.rec7 l Z).fm u).fv i v' c' (((F u).lv i hi).pr v' c' z') = ((I.rec7 l Z).fm u).fv i v' c (((F u).lv i hi).pr v' c z) := by
  intro B X I hI hP l Z H F hF hC u i hi v v' c c' γ hA hv z z' hz
  by_cases h : i = 0 ∨ i = (I.rec7 l Z).R.m
  · exact fv_off_cls ((F u).lv i hi) ((F u).cls i hi h) ((F u).fMe i hi h) ((F u).fv i hi h) v v' c c' γ (hA.1 h) hv z z' hz
  · have h1 : 1 ≤ i := by omega
    have h2 : i + 1 ≤ (I.rec7 l Z).R.m := by omega
    obtain ⟨hβ, hA'⟩ := hA.2 h1 h2
    have e := fv_off_ch ((F u).lvC i h1 h2) (F u).atT.eV ((F u).ch i h1 h2) ((F u).fMeC i h1 h2) ((F u).fvC i h1 h2)
      v v' c c' hβ γ hA' hv z z' hz
    have e1 := (pr_lvC_eq_lv I hI hP l Z H F hF hC u i h1 h2 v' c).1 z z rfl
    have e2 := (pr_lvC_eq_lv I hI hP l Z H F hF hC u i h1 h2 v' c').1 z' z' rfl
    exact (congrArg _ e2).symm.trans (e.trans (congrArg _ e1))

end GlobalTheory.Mem.Col2.HAt.FvOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeValuesKilledByLoweringPart
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLift.LowerKill

open GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate

theorem entry_eq_zero {n : ℕ} {ε : Fin n → Bool} {κ : Matrix (Fin n) (Fin n) ℂ}
    (h : κ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * κ) {a b : Fin n} (hab : ε a ≠ ε b) : κ a b = 0 := by
  have e := congrFun (congrFun h a) b
  simp only [Formalism.REAL.Jm, mul_diagonal, diagonal_mul] at e
  cases ha : ε a <;> cases hb : ε b <;> simp only [ha, hb, ne_eq, not_true_eq_false] at hab e
  · simp only [Bool.false_eq_true, if_false, if_true] at e
    linear_combination (1 / 2 : ℂ) * e
  · simp only [Bool.false_eq_true, if_false, if_true] at e
    linear_combination (-1 / 2 : ℂ) * e

theorem block_conj {n : ℕ} {ε : Fin n → Bool} {κ κ' Y : Matrix (Fin n) (Fin n) ℂ}
    (h : κ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * κ) (h' : κ' * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * κ')
    (hY : ∀ a b, ¬ (ε a = false ∧ ε b = true) → Y a b = 0) (a b : Fin n) (hab : ¬ (ε a = false ∧ ε b = true)) :
    (κ' * Y * κ) a b = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : ε d = ε b
  · rw [Matrix.mul_apply, Finset.sum_eq_zero fun c _ => ?_, zero_mul]
    by_cases hc : ε a = ε c
    · rw [hY c d (by rw [← hc, hd]; exact hab), mul_zero]
    · rw [entry_eq_zero h' hc, zero_mul]
  · rw [entry_eq_zero h hd, mul_zero]

variable {D : D7} {T : HSp D} {Sp : D.what₂.Tau → SPar}

theorem frame_mem_UH (M : DSModel T Sp) (τ : D.what₂.Tau) {κ : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hκ : κ ∈ Formalism.REAL.Kset (M.ε τ)) : (M.fr τ)⁻¹ * κ * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
  have hu : IsUnit (M.fr τ).det := (isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : κᴴ * κ = 1 := hκ.1.1
  have h2 : κᴴ * Formalism.REAL.Jm (M.ε τ) * κ = Formalism.REAL.Jm (M.ε τ) := by
    rw [Matrix.mul_assoc, ← hκ.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h3 : M.fr τ * ((M.fr τ)⁻¹ * κ * M.fr τ) = κ * M.fr τ := by
    rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu]
  show ((M.fr τ)⁻¹ * κ * M.fr τ)ᴴ * gramAt D T τ * ((M.fr τ)⁻¹ * κ * M.fr τ) = gramAt D T τ
  rw [← M.fr_gram τ]
  calc _ = (M.fr τ * ((M.fr τ)⁻¹ * κ * M.fr τ))ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * ((M.fr τ)⁻¹ * κ * M.fr τ)) := by
        rw [conjTranspose_mul (M.fr τ)]
        simp only [Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * (κᴴ * Formalism.REAL.Jm (M.ε τ) * κ) * M.fr τ := by
        rw [h3, conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h2]

theorem adAt_mem_pMinus {θ : InfFam D} (hθ : IsInfFam θ) (M : DSModel T Sp) (ρ τ : D.what₂.Tau)
    {κ : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hκ : κ ∈ Formalism.REAL.Kset (M.ε ρ))
    {Z : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hZ : Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ) :
    adAt θ (atTau θ T ρ ((M.fr ρ)⁻¹ * κ * M.fr ρ)) τ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ := by
  have hs := atTau_spec hθ T ρ (frame_mem_UH M ρ hκ)
  have hi : infMat D.sp.cm.sig T.gram (θ τ) (atTau θ T ρ ((M.fr ρ)⁻¹ * κ * M.fr ρ)) *
      infMat D.sp.cm.sig T.gram (θ τ) (atTau θ T ρ ((M.fr ρ)⁻¹ * κ * M.fr ρ))⁻¹ = 1 := by
    rw [← infMat_mul, mul_inv_cancel, infMat_one]
  unfold adAt
  by_cases c : τ = ρ
  · subst c
    have hu : IsUnit (M.fr τ).det := (isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have h1 : κ * κᴴ = 1 := hκ.1.2
    have h1' : κᴴ * κ = 1 := hκ.1.1
    have hJ : κᴴ * Formalism.REAL.Jm (M.ε τ) = Formalism.REAL.Jm (M.ε τ) * κᴴ := by
      have := congrArg conjTranspose hκ.2
      rw [conjTranspose_mul, conjTranspose_mul, Formalism.REAL.Jm_conjTranspose] at this
      exact this.symm
    rw [hs.2.1] at hi ⊢
    have hi2 : (M.fr τ)⁻¹ * κ * M.fr τ * ((M.fr τ)⁻¹ * κᴴ * M.fr τ) = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc _ κᴴ, mul_nonsing_inv_cancel_left _ _ hu, Matrix.mul_assoc,
        ← Matrix.mul_assoc κ, h1, Matrix.one_mul, nonsing_inv_mul _ hu]
    rw [← inv_eq_right_inv hi, inv_eq_right_inv hi2]
    intro a b hab
    have e : M.fr τ * ((M.fr τ)⁻¹ * κᴴ * M.fr τ * Z * ((M.fr τ)⁻¹ * κ * M.fr τ)) * (M.fr τ)⁻¹ =
        κᴴ * (M.fr τ * Z * (M.fr τ)⁻¹) * κ := by
      simp only [Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one, mul_nonsing_inv_cancel_left _ _ hu]
    rw [e]
    exact block_conj hκ.2 hJ hZ a b hab
  · rw [hs.2.2 τ c] at hi ⊢
    rw [Matrix.one_mul] at hi
    rw [hi, Matrix.one_mul, Matrix.mul_one]
    exact hZ

variable {ψ : AddChar (AF D.host.F) ℂ} {S : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {θ : InfFam D}

theorem exists_op (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    (Z : Matrix (Fin T.rank) (Fin T.rank) ℂ) : ∃ L : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → ∀ h,
      RderC θ T τ Z (fun g => thetaKO om h g f) = fun g => thetaKO om h g (L f) := by
  have key : ∀ X ∈ lieAt T τ, ∃ L : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → ∀ h,
      Rder θ T τ X (fun g => thetaKO om h g f) = fun g => thetaKO om h g (L f) := by
    intro X hX
    obtain ⟨L, hL⟩ := _root_.GlobalTheory.DefLift.Gen.exists_generator D ψ S T χS χT om hom θ hθ τ X hX
    refine ⟨L, fun f hf h => funext fun g => ?_⟩
    have := ((hL f hf).2.2.2 (h, g) 0).deriv
    simp only [Prod.mk_mul_mk, mul_one] at this
    exact this
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem T τ Z
  obtain ⟨L₁, e1⟩ := key _ h1
  obtain ⟨L₂, e2⟩ := key _ h2
  refine ⟨L₁ + Complex.I • L₂, fun f hf h => ?_⟩
  unfold RderC
  rw [e1 f hf, e2 f hf]
  funext g
  simp [thetaKO]

def killed (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (M : DSModel T Sp) {Y : Type} [AddCommGroup Y]
    [Module ℂ Y] (pt : Y →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ P, IsThetaFunO ψ S T (pt P)) : Submodule ℂ Y where
  carrier := {P | ∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ h, RderC θ T τ Z (fun g => thetaKO om h g (pt P)) = 0}
  add_mem' := by
    intro P Q hP hQ τ Z hZ h
    obtain ⟨L, hL⟩ := exists_op hom hθ τ Z
    have a := hP τ Z hZ h
    have b := hQ τ Z hZ h
    rw [hL _ (hpt _)] at a b ⊢
    funext g
    have a' := congrFun a g
    have b' := congrFun b g
    simp only [thetaKO, map_add (f := _), Pi.add_apply, Pi.zero_apply] at a' b' ⊢
    rw [a', b', add_zero]
  zero_mem' := by
    intro τ Z _ h
    obtain ⟨L, hL⟩ := exists_op hom hθ τ Z
    rw [hL _ (hpt _)]
    funext g
    simp [thetaKO]
  smul_mem' := by
    intro r P hP τ Z hZ h
    obtain ⟨L, hL⟩ := exists_op hom hθ τ Z
    have a := hP τ Z hZ h
    rw [hL _ (hpt _)] at a ⊢
    funext g
    have a' := congrFun a g
    simp only [thetaKO, map_smul, Pi.smul_apply, Pi.zero_apply] at a' ⊢
    rw [a', smul_zero]

theorem values_killed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp), LowSm M → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M → ∀ c : CoefA S, c.Is → ∀ pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ), (∀ P, IsThetaFunO ψ S T (pt P)) → ∀ (Δ : PolF D T.rank S.rank) (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank), IsIoW θ M c om (fun P => pt P) Δ io → (∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ h, RderC θ T τ Z (fun g => thetaKO om h g (pt Δ)) = 0) → ∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ (v : ∀ ρ, lowT M ρ) w h, RderC θ T τ Z (fun g => thetaKO om h g (pt (io (PiTensorProduct.tprod ℂ v) w))) = 0 := by
  intro D ψ S T χS χT om hom θ hθ Sp M h1 h2 c hc pt hpt Δ io hio hΔ τ Z hZ v w h
  classical
  obtain ⟨hS, hK, v₀, w₀, hv₀, hw₀, e₀⟩ := hio
  beta_reduce at hS hK
  let N := killed hom hθ M pt hpt
  have step1 : ∀ w, io (PiTensorProduct.tprod ℂ v₀) w ∈ N := by
    obtain ⟨-, -, -, -, -, -, -, hd, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ S hθ
    suffices hst : ∀ g, (N.comap (io (PiTensorProduct.tprod ℂ v₀))).map (c.ρ g) ≤
        N.comap (io (PiTensorProduct.tprod ℂ v₀)) by
      intro w
      refine (((hc.2.2.2.2 _ hst).resolve_left fun h0 => ?_).ge Submodule.mem_top :
        w ∈ N.comap (io (PiTensorProduct.tprod ℂ v₀)))
      have hm : w₀ ∈ N.comap (io (PiTensorProduct.tprod ℂ v₀)) := by
        show io (PiTensorProduct.tprod ℂ v₀) w₀ ∈ N
        rw [e₀]
        exact hΔ
      rw [h0, Submodule.mem_bot] at hm
      rw [hm, norm_zero] at hw₀
      exact zero_ne_one hw₀
    · rintro g _ ⟨x, hx, rfl⟩
      obtain ⟨a, ha, u, hu, rfl⟩ := hd g
      intro τ Z hZ h
      have e : (fun g => thetaKO om h g (pt (io (PiTensorProduct.tprod ℂ v₀) (c.ρ (a * u) x)))) =
          fun g => thetaKO om (h * u) g (pt (io (PiTensorProduct.tprod ℂ v₀) x)) := by
        funext g
        rw [map_mul, hc.1 a ha, one_mul, ← hS u hu]
        unfold thetaKO
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
      rw [e]
      exact hx τ Z hZ (h * u)
  let B : MultilinearMap (RingHom.id ℂ) (fun τ => lowT M τ) (PolF D T.rank S.rank) :=
    (io.flip w).compMultilinearMap (PiTensorProduct.tprod ℂ)
  refine mem_of_translates h1 h2 B N v₀ (fun ρ h0 => ?_) (step1 w) ?_ v τ Z hZ h
  · have := hv₀ ρ
    rw [h0] at this
    simp at this
  · intro ρ k hk v u hu hv τ Z hZ h
    have e : (fun g => thetaKO om h g (pt (B (Function.update v ρ u)))) =
        rTr T (atTau θ T ρ ((M.fr ρ)⁻¹ * k * M.fr ρ)) fun g => thetaKO om h g (pt (B v)) := by
      funext g
      have := hK ρ k hk v u hu w
      show om (h, g) (pt (io (PiTensorProduct.tprod ℂ (Function.update v ρ u)) w)) 0 =
        om (h, g * atTau θ T ρ ((M.fr ρ)⁻¹ * k * M.fr ρ)) (pt (io (PiTensorProduct.tprod ℂ v) w)) 0
      rw [← this, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    rw [e, RderC_rTr hθ (isRealPt_atTau hθ ρ (frame_mem_UH M ρ hk)), hv τ _ (adAt_mem_pMinus hθ M ρ τ hk hZ) h]
    rfl

end GlobalTheory.DefLift.LowerKill

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsomOfInducedHermitianBundles
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.InducedIsom

open OfModel

theorem isRatSec_lift {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (j : Z ⟶ X)
    (ρ : X.functionField ≃+* Z.functionField)
    (hρ : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint Z ∈ j ⁻¹ᵁ U) (s : Γ(X, U)),
      ρ (fnOf U hU s) = fnOf (j ⁻¹ᵁ U) hU' (j.app U s))
    (hj : j (genericPoint Z) = genericPoint X) (B : LB X) {r : (B.pull j).ι → Z.functionFieldˣ}
    (hr : IsRatSec (B.pull j) r) :
    IsRatSec B fun i => Units.map ρ.symm.toMonoidHom (r fun _ => i) := by
  intro i i' h
  have h' : genericPoint Z ∈ j ⁻¹ᵁ (B.U i ⊓ B.U i') := by
    change j (genericPoint Z) ∈ B.U i ⊓ B.U i'
    rwa [hj]
  have h₂ : genericPoint Z ∈ (B.pull j).U (fun _ => i) ⊓ (B.pull j).U (fun _ => i') :=
    ⟨Set.mem_iInter.2 fun _ => h'.1, Set.mem_iInter.2 fun _ => h'.2⟩
  have l : (B.pull j).U (fun _ => i) ⊓ (B.pull j).U (fun _ => i') ≤ j ⁻¹ᵁ (B.U i ⊓ B.U i') :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have hg : ((B.pull j).g (fun _ => i) (fun _ => i')).val = resG Z l (j.app _ (B.g i i').val) := by
    have : (B.pull j).g (fun _ => i) (fun _ => i') = res l (pullU j _ (B.g i i')) := by
      change ∏ _k : PUnit, _ = _
      exact (Fintype.prod_unique _).trans (zpow_one _)
    rw [this]
    rfl
  have e := hr (fun _ => i) (fun _ => i') h₂
  rw [hg, fnOf_resG, ← hρ _ h] at e
  apply ρ.injective
  rw [map_mul]
  exact (ρ.apply_symm_apply _).trans (e.trans (congrArg _ (ρ.apply_symm_apply _).symm))

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

end GlobalTheory.TrueGeo.InducedIsom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldOverPlaceAlgClosure
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.ResidueBar

theorem residueField_ringEquiv_fbar : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → Nonempty (IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) := by
  first
  | exact @_root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv
  | exact _root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv
  | (apply _root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv <;> assumption)
  | (intros; apply _root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ResidueFieldAlgClosed.residueField_equiv ..)

end GlobalTheory.ResidueBar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitsCompletelyOverIntermediateOfSplitsOverRat
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.SplitTower

theorem splits_completely_of_intermediate :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : ℕ), p.Prime →
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 L)).ncard = Module.finrank ℚ L →
      ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ 𝔭.asIdeal → (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L := by
  intro K L _ _ _ _ _ p hp hcount 𝔭 hp𝔭
  rw [GlobalTheory.Bauer.ncard_eq_finrank_iff K L 𝔭]
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hPdef
  have hPmax : P.IsMaximal := by
    exact PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  haveI := hPmax
  haveI : Fintype (P.primesOver (𝓞 L)) := (IsDedekindDomain.primesOver_finite P (𝓞 L)).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 L)
  rw [NumberField.RingOfIntegers.rank] at hsum
  have h1 : (P.primesOver (𝓞 L)).ncard = ∑ _q : P.primesOver (𝓞 L), 1 := by
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq]
  have hall : ∀ Q ∈ P.primesOver (𝓞 L), Q.ramificationIdx ℤ * Q.inertiaDeg ℤ = 1 := by
    rw [← hsum, h1, Finset.sum_eq_sum_iff_of_le] at hcount
    · intro Q hQ
      exact (hcount ⟨Q, hQ⟩ (Finset.mem_univ _)).symm
    · rintro ⟨Q, hQ, _⟩ -
      exact Nat.mul_pos (Ideal.ramificationIdx_pos (R := _) Q) (Ideal.inertiaDeg_pos Q _)
  intro Q hQ
  obtain ⟨hQp, hQ𝔭⟩ := hQ
  haveI := 𝔭.isPrime
  haveI h𝔭P : 𝔭.asIdeal.LiesOver P := by
    refine ⟨hPmax.eq_of_le (Ideal.IsPrime.comap _).ne_top ?_⟩
    rw [hPdef, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    simpa using hp𝔭
  haveI : Q.LiesOver P := Ideal.LiesOver.trans Q 𝔭.asIdeal P
  have h := hall Q ⟨hQp, inferInstance⟩
  rw [Ideal.ramificationIdx_tower 𝔭.asIdeal Q, Ideal.inertiaDeg_tower 𝔭.asIdeal Q] at h
  refine Nat.eq_one_of_dvd_one ?_
  rw [← h]
  exact ⟨𝔭.asIdeal.ramificationIdx ℤ * 𝔭.asIdeal.inertiaDeg ℤ, by ring⟩

end GlobalTheory.SplitTower
end

