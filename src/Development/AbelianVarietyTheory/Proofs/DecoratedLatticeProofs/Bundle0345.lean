module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFinGL
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0331
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BrEqv
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0246

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTuple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.ChartVal

theorem infM_fin' {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : k ∈ GfC V)
    (τ : D.what₂.Tau) : infM θ V hn k τ = 1 := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.infM_fin θ V k hk τ

end GlobalTheory.AdForm.ChartVal


open GlobalTheory.AdForm.ChartVal in
theorem GlobalTheory.AdForm.rd_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (i : ℕ) (hi : i ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi i, (∀ c, (fun z : FrN (I.rec7 l Z) (B.R.N i) => φ c ⟨z.1, z.2⟩) ∈ ValC _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u i)) ∧ ∀ β y, ∀ γ ∈ GQ ((I.rec7 l Z).sp.X i), ∀ c, ∀ k ∈ GinfC ((I.rec7 l Z).sp.X i), ∀ (κ : A.U i β) (y' : (I.chain l u a).Y i), IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) i hi) k) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ → A.rd θ i hi β φ y (γ * (A.h i β c * k) * κ.1) = (A.chi i β κ : ℂ) * φ c.1 y' := by
  intro B X I hok hpins l Z u a Ch A hA θ hθ i hi φ hφ
  let eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun z => ⟨z.1, z.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hV := GlobalTheory.Mem.Col2.TC.val_tied I hok hpins l Z u a i hi (A.bad i) (Ch i) (A.chOf i) (A.K i hi) eY
    ⟨A.kb i, hA.reads i hi⟩ (fun _ => rfl)
  have hF := (hV.Fi φ).1 hφ
  refine ⟨?_, ?_⟩
  · intro c
    obtain ⟨Ψ, hΨ, he⟩ := Submodule.mem_map.1 (hF (A.chOf i c))
    have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hΨ).2) ((A.K i hi (A.chOf i c)).y ⟨c, rfl⟩) (Set.mem_univ _)
    have e2 : Ψ ((A.K i hi (A.chOf i c)).y ⟨c, rfl⟩) = fun z => φ c (eY.symm z) := congrFun he ⟨c, rfl⟩
    rw [e2] at hval
    exact hval

  · intro β y γ hγ c k hk κ y' hy
    obtain ⟨Ψ, hΨ, he⟩ := Submodule.mem_map.1 (hF β)
    have hAd : Ψ ∈ AdFun (A.K i hi β).lev (embT (I.rec7 l Z)) := (Submodule.mem_inf.1 hΨ).1
    have hfun : (fun (c : {c // A.chOf i c = β}) (z : Frames (gramC (gramN (I.rec7 l Z) i hi) (embT (I.rec7 l Z)))) =>
        φ c.1 ⟨z.1, z.2⟩) = fun c => Ψ ((A.K i hi β).y c) := he.symm
    have laws := GlobalTheory.AdForm.RdLaw.rdS_laws (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X i) (B.R.N i) (rankN (I.rec7 l Z) i hi)
      (gramN (I.rec7 l Z) i hi) rfl (B.T u) (I.rec7 l Z).R.f (A.bad i) (A.K i hi β).lev {c // A.chOf i c = β}
      (A.K i hi β).y (A.K i hi β).y_bij _ (fun c z => φ c.1 ⟨z.1, z.2⟩) (hF β) ⟨y.1, y.2⟩
    obtain ⟨hL, hK, hR, -⟩ := laws
    have hκ := (hA.U i hi β κ.1).1 κ.2
    obtain ⟨hκf, κ', hκ'⟩ := hκ
    have hchi := hA.chi i hi β κ κ' hκ'
    have hval := (GlobalTheory.AdForm.rdS_val (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X i) (B.R.N i) (rankN (I.rec7 l Z) i hi)
      (gramN (I.rec7 l Z) i hi) rfl (B.T u) (I.rec7 l Z).R.f (A.bad i) (A.K i hi β).lev {c // A.chOf i c = β}
      (A.K i hi β).y (A.K i hi β).y_bij Ψ hAd ⟨y'.1, y'.2⟩ (A.h i β c)).2.2 ((A.K i hi β).y c) ⟨y'.1, y'.2⟩
      ((hA.h i hi β c).2.symm) (fun τ => by
        have h1 := infM_fin' θ ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (A.h i β c) (hA.h i hi β c).1 τ
        show y'.1 τ = infM θ _ _ (A.h i β c) τ * y'.1 τ
        erw [h1, Matrix.one_mul])
    show rdS θ _ (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y (fun c z => φ c.1 ⟨z.1, z.2⟩) ⟨y.1, y.2⟩
      (γ * (A.h i β c * k) * κ.1) = _
    have e1 := hL γ hγ (A.h i β c * k * κ.1)
    have e2 := hK κ.1 hκf κ' hκ' (A.h i β c * k)
    have e3 := hR k hk ⟨y'.1, y'.2⟩ hy (A.h i β c)
    have e5 := congrArg (fun F => rdS θ ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y F
      ⟨y'.1, y'.2⟩ (A.h i β c)) hfun
    have e6 : Ψ ((A.K i hi β).y c) ⟨y'.1, y'.2⟩ = φ c.1 y' := (congrFun (congrFun hfun c) ⟨y'.1, y'.2⟩).symm
    have e4 := e3.trans (e5.trans (hval.trans e6))
    rw [mul_assoc]
    exact e1.trans (e2.trans (congrArg₂ (· * ·) (congrArg (fun x : ℂˣ => (x : ℂ)) hchi.symm) e4))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelElementEqProdLocalParts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevelCut

variable {D : D7}

theorem tensor_prod_zero {F A B E : Type} [Field F] [CommRing A] [CommRing B] [CommRing E] [Algebra F A]
    [Algebra F B] [Algebra F E] (z : (A × B) ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z = 0)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z = 0) : z = 0 := by
  have key : ∀ z : (A × B) ⊗[F] E, z =
      (LinearMap.inl F A B).rTensor E (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      (LinearMap.inr F A B).rTensor E (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [key z, h1, h2]; simp

theorem adele_zero (z : AE D) (h1 : infPart D z = 0) (h2 : finPart D z = 0) : z = 0 :=
  tensor_prod_zero (F := D.host.F) (A := Ainf D.host.F) (B := Af D.host.F) (E := D.host.E) z h1 h2

theorem mem_GfC_of (V : HSp D) (y : GA D V) (hy : ∀ i j, infPart D ((mt V y - 1) i j) = 0) : y ∈ GfC V := by
  show infHom V y = 1
  apply Units.ext
  change (mt V y).map (infPart D) = 1
  ext i j
  have := hy i j
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem eq_one_of_parts (V : HSp D) (y : GA D V) (h1 : y ∈ GfC V) (h2 : y ∈ GinfC V) : y = 1 := by
  have k1 : (mt V y).map (infPart D) = 1 := by
    have := congrArg Units.val (show infHom V y = 1 from h1)
    exact this
  have k2 : (mt V y).map (finPart D) = 1 := by
    have := congrArg Units.val (show finHom V y = 1 from h2)
    exact this
  apply GlobalTheory.SplitCut.mt_injective
  rw [GlobalTheory.SplitCut.mt_one]
  ext i j
  apply sub_eq_zero.mp
  apply adele_zero
  · rw [RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun (k1.trans (Matrix.map_one (infPart D) (RingHom.map_zero _) (RingHom.map_one _)).symm) i) j
  · rw [RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun (k2.trans (Matrix.map_one (finPart D) (RingHom.map_zero _) (RingHom.map_one _)).symm) i) j

theorem mem_GfC_of_grpAt (V : HSp D) (P : Pl D → Prop) (x : GA D V) (hx : x ∈ grpAt V P) : x ∈ GfC V := by
  refine mem_GfC_of V x fun i j => ?_
  have h := congrArg (fun y : GL (Fin V.rank) (AE D ⧸ idAt D P) => y.1 i j) (show _ = (1 : GL _ _) from hx)
  change Ideal.Quotient.mk (idAt D P) (mt V x i j) = _ at h
  have h2 : Ideal.Quotient.mk (idAt D P) (mt V x i j) =
      Ideal.Quotient.mk (idAt D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have h4 : (mt V x - 1) i j ∈ idAt D P := by
    rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2
  exact (RingHom.mem_ker).mp (Ideal.mem_inf.mp h4).1

theorem mem_GfC_of_supp (V : HSp D) {w : Pl D} (e : AE D) (he : ∃ ε, IsPlaceIdem D w ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε)
    (y : GA D V) (hy : SuppAt e V y) : y ∈ GfC V := by
  obtain ⟨ε, ⟨α, rfl, -⟩, hε⟩ := he
  have h0 : infPart D (e + cA D e) = 0 := by
    rw [hε]
    exact TensorProduct.zero_tmul _ _
  refine mem_GfC_of V y fun i j => ?_
  rw [← hy i j, RingHom.map_mul, h0, zero_mul]

end GlobalTheory.LevelCut

namespace GlobalTheory.LevelCut

variable {D : D7}

theorem entry_mem_of (V : HSp D) (I : Ideal (AE D)) (g : GA D V) (hg : g ∈ congGrp V I) (i j : Fin V.rank) :
    (mt V g - 1) i j ∈ I := by
  have h := congrArg (fun y : GL (Fin V.rank) (AE D ⧸ I) => y.1 i j) (show _ = (1 : GL _ _) from hg)
  change Ideal.Quotient.mk I (mt V g i j) = _ at h
  have h2 : Ideal.Quotient.mk I (mt V g i j) =
      Ideal.Quotient.mk I ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2

theorem mem_of_entry (V : HSp D) (I : Ideal (AE D)) (g : GA D V) (hg : ∀ i j, (mt V g - 1) i j ∈ I) :
    g ∈ congGrp V I := by
  show (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)) (matHom V g) = 1
  apply Units.ext
  ext i j
  change Ideal.Quotient.mk I (mt V g i j) = (1 : GL (Fin V.rank) (AE D ⧸ I)).1 i j
  rw [Units.val_one]
  have h2 : Ideal.Quotient.mk I (mt V g i j) =
      Ideal.Quotient.mk I ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) :=
    Ideal.Quotient.eq.mpr (by rw [← Matrix.sub_apply]; exact hg i j)
  rw [h2]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem congGrp_le (V : HSp D) {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J :=
  fun g hg => mem_of_entry V J g fun i j => h (entry_mem_of V I g hg i j)

theorem idAt_le_idOff_compl (P Q : Pl D → Prop) (hPQ : ∀ w, Q w → ¬ P w) : idAt D P ≤ idOff D Q := by
  intro a ha
  unfold idAt at ha
  unfold idOff
  simp only [Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  intro u
  exact ha.2 ⟨u.1, hPQ u.1 u.2⟩

end GlobalTheory.LevelCut

namespace GlobalTheory.LevelCut

theorem grpAt_eq_prod_local : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ}, c.Is → v.Is → ∀ (G : Fin n → GLoc v), GPin G →
    ∀ (j' : ℕ), ∀ x ∈ grpAt (c.V j') (· ∈ v.gP), ∃ xs : Fin n → GA D (c.V j'),
      (∀ i, SuppAt (G i).q.e (c.V j') (xs i)) ∧ x = (List.ofFn xs).prod := by
  intro D c v n _ _ G hG j' x hx
  have hoff : x ∈ grpOff (c.V j') (fun w => w ∉ Set.range fun i => (G i).q.v) := by
    refine congGrp_le (c.V j') (idAt_le_idOff_compl _ _ fun w hw hP => hw ?_) hx
    obtain ⟨i, hi⟩ := (hG.places w).mp hP
    exact ⟨i, hi.symm⟩
  obtain ⟨a, ha, h, hsupp, hcomm, -, hxa, -⟩ := GlobalTheory.SplitCut.prod_of_trivOff D (c.V j') (Fin n) (fun i => (G i).q.v)
    (fun i => (G i).q.e) hG.inj (fun i => ⟨(G i).q.split, (G i).q.above⟩) x hoff
  have hperm : (Finset.univ.toList.map h).prod = (List.ofFn h).prod := by
    rw [List.ofFn_eq_map]
    refine List.Perm.prod_eq' ((List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _) (List.nodup_finRange n)
      (by ext i; simp)).map h) ?_
    exact List.Pairwise.map _ (fun i i' hii => hcomm i i' hii) (Finset.nodup_toList _)
  refine ⟨h, hsupp, ?_⟩
  have hP : (List.ofFn h).prod ∈ GfC (c.V j') := by
    refine (GfC (c.V j')).list_prod_mem fun y hy => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact mem_GfC_of_supp (c.V j') _ (G i).q.above (h i) (hsupp i)
  have hxf : x ∈ GfC (c.V j') := mem_GfC_of_grpAt _ _ x hx
  rw [hperm] at hxa
  have haf : a ∈ GfC (c.V j') := by
    have : a = x * ((List.ofFn h).prod)⁻¹ := by rw [hxa, mul_inv_cancel_right]
    rw [this]
    exact mul_mem hxf (inv_mem hP)
  rw [hxa, eq_one_of_parts _ a haf ha, one_mul]

end GlobalTheory.LevelCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawIteratedIntegrandVacuumFormBasePoints
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.VMove


set_option maxHeartbeats 4000000 in
theorem seeSaw_iteratedIntegrand_vacuumForm_base_points_alt : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂, ∀ a ∈ GinfC (c.V (j + 1)), ∀ a' ∈ GinfC (c.V (j + 1 + 1)), ∀ (φ : t.Ch j → GA D (c.X j) → ℂ) (F : GA D (c.V (j + 1 + 1)) → ℂ) Ψ₁ Ψ₂ f z, Ψ₁ = v.Ψ j P₁ 1 a → Ψ₂ = v.Ψ (j + 1) P₂ a a' → f = rTrans (a' * v.b (j + 1 + 1)) F → Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) z → Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ => t.integrand j σ h P₁ P₂ φ F (a * q₁.1) (a' * q₂.1)) (w.sc j * w.sc (j + 1) * z) := by
  intro D c v t w hc hv ht hw j σ h P₁ P₂ a ha a' ha' φ F Ψ₁ Ψ₂ f z hΨ₁ hΨ₂ hf hI
  classical
  obtain ⟨-, -, hcomm₁, -, hright₁, -⟩ := _root_.GlobalTheory.AdelicSplit.adelic_split D (c.V (j + 1))
  obtain ⟨-, -, hcomm₂, -, hright₂, -⟩ := _root_.GlobalTheory.AdelicSplit.adelic_split D (c.V (j + 1 + 1))
  have hj₁ : j + 1 < D.R.m := by omega
  have hj₂ : j + 1 + 1 < D.R.m := by omega

  have key : ∀ p₁ ∈ GfC (c.V (j + 1)), ∀ p₂ ∈ GfC (c.V (j + 1 + 1)),
      t.integrand j σ h P₁ P₂ φ F (a * (p₁ * v.b (j + 1))) (a' * (p₂ * v.b (j + 1 + 1))) =
        w.sc j * w.sc (j + 1) * ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ
          (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h)
            (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁))
            (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g p₁ p₂) (rTrans p₂ f) := by
    intro p₁ hp₁ p₂ hp₂
    have ec₁ : a * (p₁ * v.b (j + 1)) = p₁ * (a * v.b (j + 1)) := by
      rw [← mul_assoc, hcomm₁ a ha p₁ hp₁, mul_assoc]
    have ec₂ : a' * (p₂ * v.b (j + 1 + 1)) = p₂ * (a' * v.b (j + 1 + 1)) := by
      rw [← mul_assoc, hcomm₂ a' ha' p₂ hp₂, mul_assoc]
    have er : rTrans (a' * (p₂ * v.b (j + 1 + 1))) F = rTrans p₂ f := by
      rw [hf, ec₂]; funext x; simp only [rTrans, mul_assoc]
    unfold Tup.integrand
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [(hw.e j α).1, Finsupp.mapDomain_support_of_injective (mul_left_injective (v.b j)),
      Finset.sum_image (fun x _ y _ hxy => mul_right_cancel hxy), Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finsupp.mapDomain_apply_of_injective (mul_left_injective (v.b j))]
    have e₁ : (t.sBF j (σ + 1) h).om (g * v.b j, a * (p₁ * v.b (j + 1))) (t.pt j P₁) =
        w.sc j • (t.sBF j (σ + 1) h).om (g, p₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) := by
      rw [(ht.sBF j (σ + 1) h).1, ec₁,
        show ((g * v.b j, p₁ * (a * v.b (j + 1))) : GA D (c.V j) × GA D (c.V (j + 1))) =
          (g, p₁) * (1 * v.b j, a * v.b (j + 1)) by simp,
        map_mul, Module.End.mul_apply, hw.vf j hj₁ P₁ 1 (one_mem _) a ha, map_smul, hΨ₁]
    have e₂ : (t.sFB j σ h).om (a * (p₁ * v.b (j + 1)), a' * (p₂ * v.b (j + 1 + 1))) (t.pt (j + 1) P₂) =
        w.sc (j + 1) • (t.sFB j σ h).om (p₁, p₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) := by
      rw [(ht.sFB j σ h).1, ec₁, ec₂,
        show ((p₁ * (a * v.b (j + 1)), p₂ * (a' * v.b (j + 1 + 1))) : GA D (c.V (j + 1)) × GA D (c.V (j + 1 + 1))) =
          (p₁, p₂) * (a * v.b (j + 1), a' * v.b (j + 1 + 1)) by simp,
        map_mul, Module.End.mul_apply, hw.vf (j + 1) hj₂ P₂ a ha a' ha', map_smul, hΨ₂]
    have hh := (GlobalTheory.HandHom.hand_hom D c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (φ α)).1
    simp only [Chain.hand]
    rw [e₁, e₂, hh, er]
    have hp := GlobalTheory.HandHom.per_smul (c.B (j + 1 + 1) σ (idx_step h)) c.ψ (w.sc j * w.sc (j + 1)) 1
      (handFB (t.sFB j σ h) (c.vL j σ h) (handBF (t.sBF j (σ + 1) h) (c.lnk j σ h) (φ α)
        (flatBF (t.sBF j (σ + 1) h) ((t.sBF j (σ + 1) h).om (g, p₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)))))
        (flatFB (t.sFB j σ h) ((t.sFB j σ h).om (p₁, p₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)))))
      (rTrans p₂ f)
    rw [one_smul] at hp
    rw [hp]
    ring
  obtain ⟨f₁, h1, h2⟩ := hI
  haveI := hright₁ _ (hc.μf (j + 1))
  haveI := hright₂ _ (hc.μf (j + 1 + 1))
  set B₁ : GfC (c.V (j + 1)) := ⟨v.b (j + 1), hv.b (j + 1)⟩ with hB₁
  set B₂ : GfC (c.V (j + 1 + 1)) := ⟨v.b (j + 1 + 1), hv.b (j + 1 + 1)⟩ with hB₂
  refine ⟨fun q => (w.sc j * w.sc (j + 1)) * f₁ (q * B₁⁻¹), ?_, fun q => ?_⟩
  · exact (h1.mul_right B₁⁻¹).smul (w.sc j * w.sc (j + 1))
  · have := ((h2 (q * B₁⁻¹)).mul_right B₂⁻¹).smul (w.sc j * w.sc (j + 1))
    convert this using 1
    funext q₂
    have eq₁ : (q : GA D (c.V (j + 1))) = ((q * B₁⁻¹ : GfC (c.V (j + 1))) : GA D (c.V (j + 1))) * v.b (j + 1) := by
      simp [hB₁]
    have eq₂ : (q₂ : GA D (c.V (j + 1 + 1))) =
        ((q₂ * B₂⁻¹ : GfC (c.V (j + 1 + 1))) : GA D (c.V (j + 1 + 1))) * v.b (j + 1 + 1) := by
      simp [hB₂]
    rw [Pi.smul_apply, smul_eq_mul]
    beta_reduce
    rw [eq₁, eq₂]
    exact key _ (q * B₁⁻¹).2 _ (q₂ * B₂⁻¹).2

end GlobalTheory.VMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastPeriodFactorizationOfClassData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.PerXCls

variable {D : D7}

abbrev finfF (D : D7) : AE D →+* Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem mem_GinfC_iff (V : HSp D) (g : GA D V) : g ∈ GinfC V ↔ (Formalism.L2.Theta.mt V g).map (finfF D) = 1 := by
  show finHom V g = 1 ↔ _
  rw [Units.ext_iff]
  rfl

theorem map_sand {k n : ℕ} (x : Mx D k n) (m : Mx D n n) (y : Mx D n k) (hm : m.map (finfF D) = 1) :
    (x ⬝ m ⬝ y).map (finfF D) = (x ⬝ y).map (finfF D) := by
  have e1 : (x ⬝ m ⬝ y).map (finfF D) = x.map (finfF D) ⬝ m.map (finfF D) ⬝ y.map (finfF D) := by
    rw [Matrix.map_mul (f := finfF D), Matrix.map_mul (f := finfF D)]
  have e2 : (x ⬝ y).map (finfF D) = x.map (finfF D) ⬝ y.map (finfF D) := Matrix.map_mul (f := finfF D)
  rw [e1, e2, hm, Matrix.mul_one]

theorem orth_emb_mem_GinfC {S A B : HSp D} (o : OrthDec S A B) {a : GA D A} (ha : a ∈ GinfC A) :
    o.emb (a, 1) ∈ GinfC S := by
  rw [mem_GinfC_iff] at ha ⊢
  rw [OrthDec.mt_emb, Matrix.map_add _ (map_add (finfF D)), map_sand _ _ _ ha, GlobalTheory.MixModel.mt_one, Matrix.mul_one,
    ← Matrix.map_add _ (map_add (finfF D)), o.sum_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem trc_apply {V : HSp D} (e : GA D V →₀ ℂ) (f : GA D V → ℂ) (x : GA D V) :
    trc e f x = ∑ g ∈ e.support, e g * f (x * g) := by
  simp [trc, rTrans, Finset.sum_apply]

theorem isContAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  have h0 : IsContAut V (0 : GA D V → ℂ) := ⟨fun _ _ _ => rfl, continuous_const⟩
  have hadd : ∀ {f g : GA D V → ℂ}, IsContAut V f → IsContAut V g → IsContAut V (f + g) := fun hf hg =>
    ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩
  have hsm : ∀ {f : GA D V → ℂ}, IsContAut V f → ∀ c : ℂ, IsContAut V (c • f) := fun hf c =>
    ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact hsm ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add (f := _)]; exact hadd hx hy
  | zero => simpa using h0
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact hadd (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact hsm (h x) c

theorem ontoUni_of_reindex {ι K : Type} [Group K] [TopologicalSpace K] {a b : ℕ} (hab : a = b)
    (r : K → ι → Matrix (Fin a) (Fin a) ℂ)
    (hr : OntoUni (fun k τ => (r k τ).reindex (finCongr hab) (finCongr hab))) : OntoUni r := by
  subst hab
  simpa using hr

end GlobalTheory.SeeSaw.PerXCls


open GlobalTheory.SeeSaw.PerXCls in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.SeeSaw.perX_of_clsPinD : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) →
    ClsPinD t → PerX t := by
  intro D c 𝒯 t hc ht hP
  obtain ⟨ρ, hρ, hA⟩ := hP
  intro n h y v
  have hU : OntoUni (fun k : GinfC c.T => inB c.θ c.T ρ.BT k.1) :=
    ontoUni_of_reindex ρ.hT (fun k : GinfC c.T => inB c.θ c.T ρ.BT k.1) hρ.uniT
  obtain ⟨_, _, _, ν, hν1, hν2, hcls⟩ := integral_eq_classSum D c.θ c.T ρ.BT hc.inf hU
  obtain ⟨hN, hInt, hBr, hne, hblk⟩ := hρ.low n h
  have hemb : ∀ k : GinfC c.T, (c.oT n h).emb (k.1, 1) ∈ GinfC (c.X n) := fun k => orth_emb_mem_GinfC _ k.2
  let y0 : FrN D (ρ.N n) := ρ.fr n y
  have hdet : ∀ (k : GinfC c.T) τ, IsUnit ((ρ.r n h.le ((c.oT n h).emb (k.1, 1)) τ * y0.1 τ).det) := by
    intro k τ
    rw [Matrix.det_mul]
    have hu := (hρ.uni n h.le).uni ⟨_, hemb k⟩ τ
    exact (Matrix.isUnit_det_of_left_inverse (Matrix.mem_unitaryGroup_iff'.mp hu)).mul (y0.2 τ)
  let yk : GinfC c.T → FrN D (ρ.N n) := fun k => ⟨fun τ => ρ.r n h.le ((c.oT n h).emb (k.1, 1)) τ * y0.1 τ, hdet k⟩
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.KJAvg.avg_eq_mul_branch D.what₂.Tau (ρ.N n) ρ.NT hN (fun _ => 1) (fun _ => 1) (ρ.lam n) ρ.sg hInt (ρ.low n h) hBr
    hne (GinfC c.T) ν (fun k => ρ.rT k.1) hρ.uniT y0 yk
    (fun k => ⟨_, fun τ => hblk k.1 k.2 τ, fun τ => rfl⟩) (ρ.J v 1) (hρ.J v).1 (fun k => ρ.J v k.1)
    (fun k z z' hz => (hρ.J v).2 k.1 k.2 z z' hz)
  refine ⟨a, fun s ψ hψ F => ?_⟩
  obtain ⟨⟨A, hA1⟩, B, hB⟩ := hA s
  obtain ⟨hvol, hstab, hsum⟩ := hcls c.volT B.U B.cl B.h hB.reps
  have rdtr := _root_.GlobalTheory.SeeSaw.scalarForm_laws D c (t s) ρ A hc hρ hA1.1 n h.le ψ hψ
  obtain ⟨J, χ, hCT⟩ := (ht s).CT
  have hF : IsContAut c.T (F.1 v) := isContAut_multT (hCT F.2) v
  have key : ∀ β, ∫ h' in c.volT.𝓕, trc ((t s).eT n h β) (F.1 v) h' * (t s).rd n β ψ y ((c.oT n h).emb (h', 1)) ∂c.volT.μ =
      (volLev c.volT B.U : ℂ) * ∑ a', ((stabOrd B.U (B.h a') : ℕ) : ℂ)⁻¹ *
        (a * B.ell n h β a' F (ρ.low n h fun z => (t s).rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (B.h a', 1)))) := by
    intro β
    obtain ⟨hr1, -, hr3, hr4⟩ := rdtr β
    rw [hsum]
    · congr 1
      refine Finset.sum_congr rfl fun a' _ => ?_
      congr 1
      have hpt : ∀ k : GinfC c.T, trc ((t s).eT n h β) (F.1 v) (B.h a' * k.1) *
          (t s).rd n β ψ y ((c.oT n h).emb (B.h a' * k.1, 1)) =
          B.ell n h β a' F (ρ.J v k.1) * (fun z => (t s).rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (B.h a', 1))) (yk k) := by
        intro k
        rw [hB.top n h F v β a' k.1 k.2]
        congr 1
        have hm : (c.oT n h).emb (B.h a' * k.1, 1) = (c.oT n h).emb (B.h a', 1) * (c.oT n h).emb (k.1, 1) := by
          rw [← map_mul]; simp
        rw [hm]
        refine hr3 y _ _ _ (hemb k) ?_
        intro τ
        rw [Equiv.apply_symm_apply]
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact ha _ (hr4 _) _
    · refine Continuous.mul ?_ ((hr1 y).2.comp ((c.oT n h).continuous_emb.comp (continuous_id.prodMk continuous_const)))
      have : trc ((t s).eT n h β) (F.1 v) = fun x => ∑ g ∈ ((t s).eT n h β).support, (t s).eT n h β g * F.1 v (x * g) :=
        funext fun x => trc_apply _ _ x
      rw [this]
      exact continuous_finsetSum _ fun g _ => continuous_const.mul (hF.2.comp (continuous_mul_const g))
    · intro γ hγ g
      rw [trc_apply, trc_apply]
      congr 1
      · refine Finset.sum_congr rfl fun g' _ => ?_
        rw [mul_assoc, hF.1 γ hγ]
      · have hm : (c.oT n h).emb (γ * g, 1) = (c.oT n h).emb (γ, 1) * (c.oT n h).emb (g, 1) := by
          rw [← map_mul]; simp
        rw [hm, (hr1 y).1 _ ((c.oT n h).emb_mem_GQ hγ (GQ _).one_mem)]
    · intro κ hκ g
      exact hB.inv n h ψ hψ F v y β g κ hκ
  have htl := hB.tail n h ψ hψ F
  unfold Tup.perT
  rw [Finset.sum_congr rfl fun β _ => key β]
  calc _ = a * ((volLev c.volT B.U : ℂ) * ∑ β, ∑ a', ((stabOrd B.U (B.h a') : ℕ) : ℂ)⁻¹ *
        B.ell n h β a' F (ρ.low n h fun z => (t s).rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (B.h a', 1)))) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun a' _ => by ring
    _ = _ := by rw [htl]; ring
end
end

