module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0337
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0339
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.StringsTwo
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbeddingMemLevi
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.LeviBlockIdx

theorem leviEmb_mem_levi_blockIdx : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (g : Levi k (fun a => Fin (d a))), leviEmb k (stdBlocks d hd) g ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd) := by
  intro k _ _ _ _ h N d hd g
  rw [GroundTheory.Automorphic.Parabolic.mem_levi]
  intro i j hij
  obtain ⟨⟨a, x⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := (stdBlocks d hd).surjective j
  have hab : a ≠ b := by
    simpa [Zl.JC.blockIdx] using hij
  exact leviEmb_apply_ne k (stdBlocks d hd) g hab x y

end GlobalTheory.CompanionTheory.LeviBlockIdx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissible
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.GKLocalProof

theorem invT_eq_invTranspose {A : Type} [CommRing A] (N : ℕ) :
    (invT : GL (Fin N) A →* GL (Fin N) A) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose N A :=
  MonoidHom.ext fun _ => Units.ext rfl

theorem gkLocal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GKLocal k := by
  intro k _ _ _ _ hA N V _ _ π hs hi
  rw [invT_eq_invTranspose]
  exact GlobalTheory.GelfandKazhdan.equiv_contra k N V π (hA k N V π hs hi) hi

end GlobalTheory.CompanionTheory.GKLocalProof
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LpCoefficientCenterNormPreserved
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.CoeffCentral

theorem norm_coeff_central : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (p : ℝ), CoeffLp p π → ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ (v : V) (l : Module.Dual ℂ V), IsOpen {g : GL (Fin N) k | l ∘ₗ π g = l} → ‖l (π z v)‖ = ‖l v‖ := by
  intro k _ _ _ _ N V _ _ π p h z hz v l hl
  borelize (AdGL k N)
  obtain ⟨F, hF, -⟩ := h MeasureTheory.Measure.haar inferInstance v l hl
  have h1 : (QuotientGroup.mk z : AdGL k N) = QuotientGroup.mk 1 := by
    rw [QuotientGroup.mk_one]
    exact (QuotientGroup.eq_one_iff z).2 hz
  have h2 := hF z
  rw [h1, hF 1] at h2
  simpa using h2.symm

end GlobalTheory.CompanionTheory.CoeffCentral
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapMemKfin
section
noncomputable section

open Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.GLK

open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

def expG (X : Mat n) (t : ℝ) : G n := (Matrix.isUnit_exp ((t : ℂ) • X)).unit

def e1 {V : Type} [AddCommGroup V] [Module ℂ V] (D : Mat n → Module.End ℂ V) (a b : Fin n) : Module.End ℂ V :=
  (1 / 2 : ℂ) • (D (Matrix.single a b 1) - Complex.I • D (Matrix.single a b Complex.I))

def f1 {V : Type} [AddCommGroup V] [Module ℂ V] (D : Mat n → Module.End ℂ V) (a b : Fin n) : Module.End ℂ V :=
  (1 / 2 : ℂ) • (D (Matrix.single a b 1) + Complex.I • D (Matrix.single a b Complex.I))

def e2 {V : Type} [AddCommGroup V] [Module ℂ V] (D : Mat n → Module.End ℂ V) (a b : Fin n) : Module.End ℂ V :=
  -f1 D b a

end GlobalTheory.CompanionTheory.GLK

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientCartanTranslate
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.CongruenceCoef

theorem conj_mem_Km (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N m : ℕ) {p x : GL (Fin N) k}
    (hp : p ∈ KO k (Fin N)) (hx : x ∈ Zls.Km k N m) : p * x * p⁻¹ ∈ Zls.Km k N m := by
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨b, hb, rfl⟩ := hx
  refine ⟨a * b * a⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  exact (MonoidHom.normal_ker _).conj_mem b hb a

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (H : Subgroup G) (v : V) :
    v ∈ fixed π H ↔ ∀ h ∈ H, π h v = v := by
  constructor
  · intro hv h hh
    have := hv ⟨h, hh⟩
    simpa using this
  · intro hv h
    simpa using hv h h.2

theorem coef_const_translated_double_coset :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), ∀ (m : ℕ) (v : V), v ∈ fixed π (Zls.Km k N m) → ∀ l : Module.Dual ℂ V, (∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l) → ∀ (p1 p2 : GL (Fin N) k), p1 ∈ KO k (Fin N) → p2 ∈ KO k (Fin N) → (π p2 v ∈ fixed π (Zls.Km k N m)) ∧ (∀ x ∈ Zls.Km k N m, (l ∘ₗ π p1) ∘ₗ π x = l ∘ₗ π p1) ∧ ∀ (D : GL (Fin N) k), ∀ x ∈ Zls.Km k N m, ∀ y ∈ Zls.Km k N m, l (π (p1 * x * D * y * p2) v) = (l ∘ₗ π p1) (π D (π p2 v)) := by
  intro k _ _ _ _ N V _ _ π m v hv l hl p1 p2 hp1 hp2
  have hv' := (mem_fixed_iff π _ v).1 hv
  have h1 : ∀ y ∈ Zls.Km k N m, π y (π p2 v) = π p2 v := by
    intro y hy
    have hc : p2⁻¹ * y * p2⁻¹⁻¹ ∈ Zls.Km k N m := conj_mem_Km k N m (inv_mem hp2) hy
    have e : y * p2 = p2 * (p2⁻¹ * y * p2⁻¹⁻¹) := by group
    have h := hv' _ hc
    calc π y (π p2 v) = π (y * p2) v := by rw [map_mul, Module.End.mul_apply]
      _ = π p2 (π (p2⁻¹ * y * p2⁻¹⁻¹) v) := by rw [e, map_mul, Module.End.mul_apply]
      _ = π p2 v := by rw [h]
  have h2 : ∀ x ∈ Zls.Km k N m, (l ∘ₗ π p1) ∘ₗ π x = l ∘ₗ π p1 := by
    intro x hx
    have hc : p1 * x * p1⁻¹ ∈ Zls.Km k N m := conj_mem_Km k N m hp1 hx
    have e : p1 * x = (p1 * x * p1⁻¹) * p1 := by group
    have h := hl _ hc
    ext w
    have hw := LinearMap.congr_fun h (π p1 w)
    simp only [LinearMap.comp_apply] at hw ⊢
    calc l (π p1 (π x w)) = l (π (p1 * x) w) := by rw [map_mul, Module.End.mul_apply]
      _ = l (π (p1 * x * p1⁻¹) (π p1 w)) := by rw [e, map_mul, Module.End.mul_apply]; simp
      _ = l (π p1 w) := hw
  refine ⟨(mem_fixed_iff π _ _).2 h1, h2, ?_⟩
  intro D x hx y hy
  have h3 := LinearMap.congr_fun (h2 x hx) (π D (π p2 v))
  simp only [LinearMap.comp_apply] at h3
  have e : π (p1 * x * D * y * p2) v = π p1 (π x (π D (π y (π p2 v)))) := by
    simp only [map_mul, Module.End.mul_apply]
  rw [e, h1 y hy, h3]
  simp only [LinearMap.comp_apply]

end GlobalTheory.CompanionTheory.CongruenceCoef
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableSdot
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

namespace GlobalTheory.CompanionTheory.RatDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem thetaA_ratGL (g : GL (Fin n) E) : thetaA E n (ratGL E n g) = ratGL E n (thetaE E n g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [thetaR_val, ← map_inv]
  exact conjAd_algebraMap _

theorem ratCent_le (d : GL (Fin n) E) : ratCent d ≤ adCent d := by
  rintro _ ⟨g, hg, rfl⟩
  have h : twConj (thetaE E n) g d = d := hg
  change twConj (thetaA E n) (ratGL E n g) (ratGL E n d) = ratGL E n d
  rw [twConj, thetaA_ratGL, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg _ h

theorem discrete_ratIn (d : GL (Fin n) E) : DiscreteTopology (ratIn d) := by
  haveI := GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (E := E) (n := n)
  have hmem : ∀ x : ratIn d, (x.1.1 : GA E n) ∈ (ratGL E n).range := fun x => by
    obtain ⟨g, -, hg⟩ := (Subgroup.mem_subgroupOf.1 x.2)
    exact ⟨g, hg⟩
  refine DiscreteTopology.of_continuous_injective
    (f := fun x : ratIn d => (⟨x.1.1, hmem x⟩ : (ratGL E n).range)) ?_ ?_
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro x y h
    have h' : (x.1.1 : GA E n) = y.1.1 := congrArg (fun z : (ratGL E n).range => (z : GA E n)) h
    exact Subtype.ext (Subtype.ext h')

theorem isClosed_adCent (d : GL (Fin n) E) : IsClosed (adCent d : Set (GA E n)) := by
  haveI : T2Space (GA E n) := by
    haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
    exact Units.isEmbedding_embedProduct.t2Space
  have hc : Continuous fun g : GA E n => twConj (thetaA E n) g (ratGL E n d) := by
    unfold twConj
    exact (continuous_inv.mul continuous_const).mul GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA
  exact isClosed_eq hc continuous_const

theorem measurable_sdot {m : ℕ} (e : Fin m → SignType) :
    Measurable fun p : ((Fin m → SignType) → ℝ) × (Fin m → ℝ) => sdot e p.2 := by
  unfold sdot
  exact Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp measurable_snd).const_mul _

theorem measurable_gam (m : ℕ) :
    Measurable fun p : ((Fin m → SignType) → ℝ) × (Fin m → ℝ) => gam p.1 p.2 := by
  classical
  unfold gam gamOn
  refine Finset.measurable_sum _ fun s _ => ?_
  refine Measurable.const_mul (Finset.measurable_prod _ fun e _ => ?_) _
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_lt ((measurable_pi_apply e).comp measurable_fst) (measurable_sdot e)

theorem ratDisc : PositivityTheory.Rg.BcB.D4.RatDisc :=
  ⟨fun _ _ _ _ _ d => ⟨ratCent_le d, discrete_ratIn d, isClosed_adCent d⟩, measurable_gam⟩

end GlobalTheory.CompanionTheory.RatDisc

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelDerivativeZero
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMir

theorem mem_MirUin_iff_mem_derUnipM (k : Type) [Field k] (n : ℕ) (g : Mir k n) :
    g ∈ MirUin k n ↔ g ∈ derUnipM k n n := by
  rw [MirUin, derUnipM, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, derUnip, Subgroup.mem_inf]
  constructor
  · rintro ⟨v, hv⟩
    rw [← hv]
    refine ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, fun i hi => ?_⟩
    · have hj : j ≠ Fin.last n := fun h => by
        subst h; exact absurd hji (not_lt.2 (Fin.le_last i))
      have hij : i ≠ j := (ne_of_lt hji).symm
      simp [unip, colMat, Matrix.one_apply, hj, hij]
    · by_cases hi : i = Fin.last n
      · subst hi; simp [unip, colMat]
      · simp [unip, colMat, hi]
    · have hi' : i ≠ Fin.last n := fun h => by subst h; simp at hi
      ext l
      simp [unip, colMat, hi', Matrix.col, Matrix.one_apply, Pi.single_apply, eq_comm]
  · rintro ⟨hB, hC⟩
    refine ⟨Multiplicative.ofAdd (fun i => (g : GL (Fin (n + 1)) k).val (Fin.castSucc i) (Fin.last n)), ?_⟩
    ext i j
    show (1 + colMat k n _) i j = _
    induction j using Fin.lastCases with
    | last =>
      induction i using Fin.lastCases with
      | last => simp [colMat, ((mem_unipB k).1 hB).2]
      | cast i => simp [colMat, Matrix.one_apply, Fin.castSucc_ne_last]
    | cast j =>
      have h := congrFun (hC (Fin.castSucc j) (by simp)) i
      rw [mulVec_single_one] at h
      simp only [Matrix.col_apply] at h
      rw [h]
      simp [colMat, Fin.castSucc_ne_last, Matrix.one_apply, Pi.single_apply]

theorem derCharM_self_apply {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (n : ℕ) (x : derUnipM k n n) : derCharM k ψ n n x = 1 := by
  change Circle.toUnits (ψ (∑ p ∈ Finset.univ.filter
    (fun p : Fin (n + 1) × Fin (n + 1) => (p.2 : ℕ) = p.1 + 1 ∧ n ≤ (p.1 : ℕ)), _)) = 1
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  have h := (Finset.mem_filter.1 hp).2
  have := p.2.isLt
  omega

theorem twKer_MirUin_eq_derUnipM (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k n) V) :
    twKer τ (MirUin k n) 1 = twKer τ (derUnipM k n n) (derCharM k ψ n n) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w ⟨u, v, rfl⟩
    refine Submodule.subset_span ⟨⟨u, (mem_MirUin_iff_mem_derUnipM k n u).1 u.2⟩, v, ?_⟩
    simp [derCharM_self_apply]
  · refine Submodule.span_le.2 ?_
    rintro w ⟨u, v, rfl⟩
    refine Submodule.subset_span ⟨⟨u, (mem_MirUin_iff_mem_derUnipM k n u).2 u.2⟩, v, ?_⟩
    simp [derCharM_self_apply]

end GlobalTheory.CompanionTheory.BZMir
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusContractingBlockLtOne
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JCModulus

theorem prod_zpow_eq {ι : Type*} {x : ℝ} (hx : x ≠ 0) (s : Finset ι) (f : ι → ℤ) :
    ∏ a ∈ s, x ^ f a = x ^ ∑ a ∈ s, f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hx, ih]

theorem exponent_eq {h : ℕ} (d : Fin h → ℕ) (j : Fin h) :
    ∑ a, (if a ≤ j then (d a : ℤ) * modExp (fun a => Fin (d a)) a else 0) =
      (∑ a with a ≤ j, (d a : ℤ)) * ∑ b with j < b, (d b : ℤ) := by
  set f : Fin h → Fin h → ℤ := fun a b =>
    (d a : ℤ) * ((d b : ℤ) * ((if a < b then 1 else 0) - (if b < a then 1 else 0))) with hf
  have hm : ∀ a, (d a : ℤ) * modExp (fun a => Fin (d a)) a = ∑ b, f a b := by
    intro a
    rw [← Finset.mul_sum]
    congr 1
    simp [modExp, Finset.sum_filter, mul_sub, Finset.sum_sub_distrib]
  have hanti : ∀ a b, f b a = - f a b := by
    intro a b
    simp only [hf]
    ring
  have hcancel : ∑ a with a ≤ j, ∑ b with b ≤ j, f a b = 0 := by
    have h1 : ∑ a with a ≤ j, ∑ b with b ≤ j, f a b = ∑ a with a ≤ j, ∑ b with b ≤ j, f b a :=
      Finset.sum_comm
    have h2 : ∑ a with a ≤ j, ∑ b with b ≤ j, f b a = - ∑ a with a ≤ j, ∑ b with b ≤ j, f a b := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => hanti a b
    omega
  have hcross : ∑ a with a ≤ j, ∑ b with j < b, f a b =
      (∑ a with a ≤ j, (d a : ℤ)) * ∑ b with j < b, (d b : ℤ) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    have hab : a < b := lt_of_le_of_lt (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
    simp [hf, hab, hab.not_gt]
  calc ∑ a, (if a ≤ j then (d a : ℤ) * modExp (fun a => Fin (d a)) a else 0)
      = ∑ a with a ≤ j, ∑ b, f a b := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun a _ => by rw [hm]
    _ = ∑ a with a ≤ j, ((∑ b with b ≤ j, f a b) + ∑ b with j < b, f a b) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ≤ j)]
        simp only [not_le]
    _ = _ := by rw [Finset.sum_add_distrib, hcancel, zero_add, hcross]

theorem nabs_lt_one_of_valuation_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : kˣ) (ht : ValuativeRel.valuation k (t : k) < 1) :
    nabs k t < 1 := by
  obtain ⟨-, -, hle, hone, -⟩ := nabs_properties k
  have h1 : nabs k (1 : kˣ) = 1 := (hone 1).2 (by simp)
  refine lt_of_le_of_ne ?_ fun h => ht.ne ((hone t).1 h)
  rw [← h1]
  exact (hle t 1).2 (by simpa using ht.le)

theorem modulus_zj_lt_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) →
    ∀ (t : kˣ), ValuativeRel.valuation k (t : k) < 1 → ∀ (j : Fin h), j.val + 1 < h →
    modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) < 1 := by
  intro k _ _ _ _ h N d _ hpos t ht j hj
  have hx1 := nabs_lt_one_of_valuation_lt_one k t ht
  obtain ⟨hmul, hx0', -, hone, -⟩ := nabs_properties k
  have hx0 := hx0' t
  have hdet : ∀ a, nabs k (Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a)) =
      if a ≤ j then nabs k t ^ d a else 1 := by
    intro a
    have hpow : ∀ n : ℕ, nabs k (t ^ n) = nabs k t ^ n := by
      intro n
      induction n with
      | zero => simpa using (hone 1).2 (by simp)
      | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
    by_cases ha : a ≤ j
    · have h1 : Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a) = t ^ d a := by
        apply Units.ext
        simp [Zl.JC.zj, ha, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.det_diagonal]
      rw [h1, hpow, if_pos ha]
    · have h1 : Zl.JC.zj d t j a = 1 := by simp [Zl.JC.zj, ha]
      rw [h1, if_neg ha, map_one]
      exact (hone 1).2 (by simp)
  have hE : 0 < (∑ a with a ≤ j, (d a : ℤ)) * ∑ b with j < b, (d b : ℤ) := by
    refine mul_pos (Finset.sum_pos (fun a _ => by exact_mod_cast hpos a) ⟨j, by simp⟩)
      (Finset.sum_pos (fun a _ => by exact_mod_cast hpos a) ⟨⟨j.val + 1, hj⟩, ?_⟩)
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.lt_def.2 (Nat.lt_succ_self _)⟩
  have hmod : modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) =
      nabs k t ^ ((∑ a with a ≤ j, (d a : ℤ)) * ∑ b with j < b, (d b : ℤ)) := by
    rw [← exponent_eq, ← prod_zpow_eq hx0.ne']
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [hdet]
    split_ifs with ha
    · rw [zpow_mul, zpow_natCast]
    · simp
  rw [hmod]
  exact zpow_lt_one₀ hx0 hx1 hE

end GlobalTheory.CompanionTheory.JCModulus
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetOfStringsDeterminesPointsDegreesStatement
section
open GlobalTheory.DiscSpec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiset_of_strings_determines_points_degrees : ∀ {X ι κ : Type} [Fintype ι] [Fintype κ] (p : ι → X) (d : ι → ℕ) (p' : κ → X) (d' : κ → ℕ), (∀ i, 1 ≤ d i) → (∀ j, 1 ≤ d' j) → GlobalTheory.Rigid.strings p d = GlobalTheory.Rigid.strings p' d' → ∃ s : ι ≃ κ, ∀ i, p i = p' (s i) ∧ d i = d' (s i) := by
  first | exact @GlobalTheory.CompanionTheory.Rigid.strings_rigid | exact GlobalTheory.CompanionTheory.Rigid.strings_rigid | (intros; apply GlobalTheory.CompanionTheory.Rigid.strings_rigid <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedWordLettersCuspidal
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.ZcWords

theorem wtW_isCusp {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h : ℕ} (Δ : Fin h → Segment k) :
    ∀ c ∈ wtW Δ, c.IsCusp := by
  intro c hc
  obtain ⟨l, hl, hcl⟩ := List.mem_flatten.1 hc
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hl
  obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hcl
  exact Segment.isCusp_term _ _

end GlobalTheory.CompanionTheory.ZcWords
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiTensorCentralBlockScalar
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JCScalar

theorem piTensor_zj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h : ℕ} (x : Fin h → IrrGL (k := k)) (t : kˣ) (c : Fin h → ℂ), (∀ i, Zl.ScalarBy (x i) t (c i)) → ∀ (j : Fin h) (v : PiTensorProduct ℂ (fun a => (x a).2.rep.V)), piTensor (fun a => (x a).rep) (Zl.JC.zj (fun a => (x a).1) t j) v = (∏ i ∈ Finset.univ.filter (· ≤ j), c i) • v := by
  intro k _ _ _ _ h x t c hc j v
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, smul_comm, piTensor_tprod]
    congr 1
    have hf : ∀ a, (x a).rep (Zl.JC.zj (fun a => (x a).1) t j a) (f a)
        = (if a ≤ j then c a else 1) • f a := by
      intro a
      by_cases ha : a ≤ j
      · simp only [Zl.JC.zj, if_pos ha]
        exact hc a (f a)
      · simp [Zl.JC.zj, if_neg ha]
    simp only [hf]
    rw [MultilinearMap.map_smul_univ, Finset.prod_filter]
    simp only [RingHom.id_apply]
  | add a b ha hb => rw [map_add (f := _), ha, hb, smul_add]

end GlobalTheory.CompanionTheory.JCScalar
end

