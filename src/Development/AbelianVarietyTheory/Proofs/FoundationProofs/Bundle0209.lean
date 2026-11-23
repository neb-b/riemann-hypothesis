module

public import Mathlib
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0207
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
public import Formalism.LocalToGlobal.Columns.PolyFn

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalConjugationSelfDualLatticesHost
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalConjugacy
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

noncomputable def coordLat (V : Formalism.BasicNotions.HSpace E) (L : Submodule (𝓞 E) V.V) : Submodule (𝓞 E) (Fin V.rank → E) :=
  L.map (V.frame.equivFun.restrictScalars (𝓞 E)).toLinearMap

theorem span_eq_top_of_unimodular (V : Formalism.BasicNotions.HSpace E)
    (L : Submodule (𝓞 E) V.V) (h : Submodule.IsLattice E L)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) :
    Submodule.span E (L : Set V.V) = ⊤ := by
  classical
  by_contra hspan
  obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis V.hT V.nondeg V.frame
  let μ := ∑ j, star (φ (V.frame j)) • bs j
  have hμ : ∀ v, V.hT μ v = φ v := by
    have key : V.hT μ = φ := by
      apply V.frame.ext
      intro i
      dsimp only [μ]
      rw [map_sum, LinearMap.sum_apply]
      have hs : ∀ j, V.hT (star (φ (V.frame j)) • bs j) (V.frame i) =
          φ (V.frame j) * (if i = j then 1 else 0) := by
        intro j
        rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
        congr 1
        rw [← V.herm.eq (V.frame i) (bs j), hbs]
        split_ifs <;> simp
      simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact fun v => congrArg (fun f : V.V →ₗ[E] E => f v) key
  have hμ₀ : μ ≠ 0 := by
    intro hz
    apply hφ₀
    ext y
    simpa [hz] using (hμ y).symm
  have hline (a : E) : a • μ ∈ L := by
    rw [← hu]
    change a • μ ∈ Formalism.E.hdual V.hT L
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    intro y hy
    have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
    simp [← V.herm.eq (a • μ) y, LinearMap.map_smulₛₗ, hμ, hy₀]
  let i : E →ₗ[𝓞 E] L :=
    ((LinearMap.toSpanSingleton E _ μ).restrictScalars (𝓞 E)).codRestrict L hline
  let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr h.fg
  let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
    smul_left_injective E hμ₀ (congrArg Subtype.val hab)
  exact RingOfIntegers.not_isField E
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))

theorem isLattice_coordLat (V : Formalism.BasicNotions.HSpace E) (L : Submodule (𝓞 E) V.V)
    (h : Submodule.IsLattice E L)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L := by exact V.baseLattice_isUnimodular) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice (coordLat V L) := by
  refine ⟨h.fg.map _, ?_⟩
  have : (coordLat V L : Set (Fin V.rank → E)) = V.frame.equivFun.toLinearMap '' (L : Set V.V) := rfl
  rw [this, ← Submodule.map_span, span_eq_top_of_unimodular V L h hu, Submodule.map_top, LinearEquiv.range]

theorem herm_coord (V : Formalism.BasicNotions.HSpace E) (x y : V.V) :
    herm V.gramᵀ (V.frame.equivFun x) (V.frame.equivFun y) = V.hT y x := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord, herm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change V.frame.repr x j * V.gram i j * star (V.frame.repr y i) = _
  ring

theorem selfDual_coordLat (V : Formalism.BasicNotions.HSpace E) (L : Submodule (𝓞 E) V.V)
    (h : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) (x : Fin V.rank → E) :
    x ∈ coordLat V L ↔ ∀ y ∈ coordLat V L, IsIntegral ℤ (herm V.gramᵀ x y) := by
  obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective x
  have h1 : V.frame.equivFun x ∈ coordLat V L ↔ x ∈ L :=
    ⟨fun ⟨z, hz, e⟩ => V.frame.equivFun.injective e ▸ hz, fun hx => ⟨x, hx, rfl⟩⟩
  have h2 : x ∈ L ↔ ∀ y ∈ L, V.hT y x ∈ (1 : Submodule (𝓞 E) E) := by
    conv_lhs => rw [← show Formalism.HermitianLatticesTheory.dual V.hT L = L from h]
    simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]
  have h3 : ∀ z : E, z ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ z := fun z =>
    Submodule.mem_one.trans ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  rw [h1, h2]
  constructor
  · rintro H _ ⟨y, hy, rfl⟩
    have := (h3 _).1 (H y hy)
    rwa [← herm_coord] at this
  · intro H y hy
    rw [h3, ← herm_coord]
    exact H _ ⟨y, hy, rfl⟩

theorem mem_latLoc_iff (V : Formalism.BasicNotions.HSpace E) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (y : Fin V.rank → LocAlg v) :
    y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) V v ↔ y ∈ locLattice v (coordLat V V.L0) := by
  have key : ∀ (a : v.adicCompletionIntegers (maximalRealSubfield E)) (b : v.adicCompletion (maximalRealSubfield E)) (z : E),
      a • (b ⊗ₜ[maximalRealSubfield E] z : LocAlg v) = ((a : v.adicCompletion (maximalRealSubfield E)) * b) ⊗ₜ z := by
    intro a b z
    rw [TensorProduct.smul_tmul']
    rfl
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have := Submodule.smul_mem (locLattice v (coordLat V V.L0)) (⟨a, ha⟩ : v.adicCompletionIntegers (maximalRealSubfield E))
        (Submodule.subset_span ⟨_, ⟨x, hx, rfl⟩, rfl⟩)
      convert this using 1
      funext i
      simp only [Pi.smul_apply, locEmb_apply, key, mul_one]
      rfl
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  · intro hy
    suffices H : ∀ a : v.adicCompletionIntegers (maximalRealSubfield E),
        a • y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) V v by
      simpa using H 1
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hy
      intro a
      refine AddSubgroup.subset_closure ⟨a, a.2, x, hx, ?_⟩
      funext i
      simp only [Pi.smul_apply, locEmb_apply, key, mul_one]
      rfl
    | zero => intro a; rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => intro a; rw [smul_add]; exact add_mem (hx a) (hy a)
    | smul c x _ hx => intro a; rw [smul_smul]; exact hx _

theorem exists_conj (hc : CMData (maximalRealSubfield E) E) (V : Formalism.BasicNotions.HSpace E)
    (L : Submodule (𝓞 E) V.V) (h1 : Submodule.IsLattice E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) :
    ∃ γ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), HA (Fv (maximalRealSubfield E) v) hc.sig V.gram,
      {v | γ v ≠ 1}.Finite ∧ ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
        (y : Fin V.rank → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E),
        y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) V v ↔
          (HA.mat (Fv (maximalRealSubfield E) v) hc.sig V.gram (γ v)).1.mulVec y ∈
            GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) (GlobalTheory.VolRatioCompare.reLat V L h1 h2) v := by
  haveI : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
    Formalism.L2.Pj.unramBridge_holds E fun P hP => by
      obtain ⟨θ, t, e1, e2⟩ := hc.cmUnram.2.2 P hP
      refine ⟨θ, ?_⟩
      have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) θ = t :=
        RingOfIntegers.ext e1.symm
      rwa [this]
  have hG : ∀ a b, cc (V.gramᵀ a b) = V.gramᵀ b a := fun a b => V.herm.eq (V.frame b) (V.frame a)
  have hd : V.gramᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero
  obtain ⟨γ, hγ, hfin⟩ := (GlobalTheory.selfDual_lattices_one_genus hG hG hd hd (isLattice_coordLat V L h1 h2)
    (isLattice_coordLat V V.L0 V.standardTuple_isLattice V.baseLattice_isUnimodular)
    (Or.inl ⟨selfDual_coordLat V L h2, selfDual_coordLat V V.L0 V.baseLattice_isUnimodular⟩)).2.1 rfl
  have hmem : ∀ v, γ v ∈ HR (Fv (maximalRealSubfield E) v) hc.sig V.gram := fun v => by
    have h := congrArg Matrix.transpose (hγ v).1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h
    exact h.symm
  refine ⟨fun v => ⟨γ v, hmem v⟩, hfin.subset fun v hv h => hv (Subtype.ext h), fun v y => ?_⟩
  rw [mem_latLoc_iff]
  exact ((hγ v).2 y).trans (mem_latLoc_iff (GlobalTheory.VolRatioCompare.reLat V L h1 h2) v _).symm

end

theorem exists_local_conjugation : ∀ (D : D7) (V : HSp D) (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L), ∃ γ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), HA (Fv D.host.F v) D.sp.cm.sig V.gram, {v | γ v ≠ 1}.Finite ∧ ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (y : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E), y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) V v ↔ (HA.mat (Fv D.host.F v) D.sp.cm.sig V.gram (γ v)).1.mulVec y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) (GlobalTheory.VolRatioCompare.reLat V L h1 h2) v :=
  fun D V L h1 h2 =>
    haveI : IsCMField D.host.E := D.host.isCMField_hostE
    exists_conj (E := D.host.E) D.sp.cm V L h1 h2

end GlobalTheory.LocalConjugacy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroMapEqZeroOfWeightNe
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem rowDiv_eq_zero_of_unipotent_fixed {n : ℕ} (nu : DomWeight n) (q : MvPolynomial (Fin n × Fin n) ℂ)
    (hq : ∀ g : GL (Fin n) ℂ, (g : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id →
      (∀ a, (g : Matrix (Fin n) (Fin n) ℂ) a a = 1) → sqAct ℂ n nu g q = q)
    (a b : Fin n) (hab : a < b) (k : ℕ) (hk : 1 ≤ k) : rowDiv ℂ a b k q = 0 := by
  have hfix : ∀ t : ℂ, rowAct ℂ (lfockq_mat a b t) q = q := by
    intro t
    have htri : (lfockq_mat a b t).transpose.BlockTriangular id := by
      intro i j hij
      have hij' : j < i := hij
      simp only [Matrix.transpose_apply, lfockq_mat]
      rw [if_neg hij'.ne, if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hab hij'
    have hdiag : ∀ i, (lfockq_mat a b t).transpose i i = 1 := by
      intro i
      simp only [Matrix.transpose_apply, lfockq_mat]
      rw [if_pos trivial, if_neg, add_zero]
      rintro ⟨h1, h2⟩
      exact hab.ne (h2.symm.trans h1)
    have hdet : (lfockq_mat a b t).transpose.det = 1 := by
      rw [Matrix.det_of_upperTriangular htri]
      simp only [hdiag, Finset.prod_const_one]
    let g : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet ▸ one_ne_zero :
      (lfockq_mat a b t).transpose.det ≠ 0)
    have hg : (g : Matrix (Fin n) (Fin n) ℂ) = (lfockq_mat a b t).transpose := rfl
    have hd : Matrix.GeneralLinearGroup.det g = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hg, hdet, Units.val_one]
    have := hq g htri hdiag
    unfold sqAct at this
    rwa [detPow, hd, one_zpow, Units.val_one, one_smul, hg, Matrix.transpose_transpose] at this
  have hP : rowGen ℂ a b q = Polynomial.C q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective
      (C_injective (Fin n × Fin n) ℂ))
    rintro _ ⟨t, rfl⟩
    show Polynomial.eval _ _ = Polynomial.eval _ _
    rw [lfockq_eval_rowGen, hfix, Polynomial.eval_C]
  rw [rowDiv, hP, Polynomial.coeff_C, if_neg (by omega)]

theorem exists_ne_zero_map_eq_zero_of_weight_ne (n : ℕ) (mu nu : DomWeight n) (hne : mu ≠ nu)
    (φ : (sqRep ℂ n mu).IntertwiningMap (sqRep ℂ n nu)) :
    ∃ f : nablaSq ℂ n mu, f ≠ 0 ∧ φ f = 0 := by
  let f : nablaSq ℂ n mu := ⟨extremal ℂ n mu, hwMem ℂ n n le_rfl _ (factNatW n mu).1⟩
  refine ⟨f, fun h => hwNe ℂ n n le_rfl mu.natW (congrArg Subtype.val h), ?_⟩
  have hint : ∀ g x, φ (sqRep ℂ n mu g x) = sqRep ℂ n nu g (φ x) := fun g x =>
    Representation.IntertwiningMap.isIntertwining _ _ φ g x
  obtain ⟨c, hc⟩ : ∃ c : ℂ, (φ f : MvPolynomial (Fin n × Fin n) ℂ) = c • extremal ℂ n nu := by
    apply hwLine ℂ n n le_rfl nu.natW (factNatW n nu).1 _ (φ f).2
    intro a b hab k hk
    refine rowDiv_eq_zero_of_unipotent_fixed nu _ (fun g h1 h2 => ?_) a b hab k hk
    have e : sqRep ℂ n mu g f = f := Subtype.ext ((factSqHighestWeight ℂ n mu).2 g h1 h2)
    rw [← sqRep_coe, ← hint, e]
  obtain ⟨i, hi⟩ : ∃ i, mu.w i ≠ nu.w i := by
    by_contra h
    push Not at h
    apply hne
    obtain ⟨w, hw⟩ := mu
    obtain ⟨w', hw'⟩ := nu
    have : w = w' := funext h
    subst this
    rfl
  let u : ℂˣ := Units.mk0 2 two_ne_zero
  let t : Fin n → ℂˣ := fun a => if a = i then u else 1
  have hprod : ∀ lam : DomWeight n, ((∏ a, (t a) ^ (lam.w a) : ℂˣ) : ℂ) = (2 : ℂ) ^ lam.w i := by
    intro lam
    rw [Finset.prod_eq_single i (fun b _ hb => by simp [t, hb]) (by simp)]
    simp [t, u]
  have e : sqRep ℂ n mu (diagGL ℂ n t) f = (2 : ℂ) ^ mu.w i • f := by
    apply Subtype.ext
    rw [← hprod]
    exact (factSqHighestWeight ℂ n mu).1 t
  have e2 : sqRep ℂ n nu (diagGL ℂ n t) (φ f) = (2 : ℂ) ^ nu.w i • φ f := by
    let h : nablaSq ℂ n nu := ⟨extremal ℂ n nu, hwMem ℂ n n le_rfl _ (factNatW n nu).1⟩
    have hc' : φ f = c • h := Subtype.ext hc
    have e3 : sqRep ℂ n nu (diagGL ℂ n t) h = (2 : ℂ) ^ nu.w i • h := by
      apply Subtype.ext
      rw [← hprod]
      exact (factSqHighestWeight ℂ n nu).1 t
    rw [hc', map_smul, e3, smul_comm]
  have e4 := hint (diagGL ℂ n t) f
  rw [e, e2, map_smul, ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at e4
  refine e4.resolve_left fun h => hi ?_
  have h' : ((2 : ℝ) ^ mu.w i) = (2 : ℝ) ^ nu.w i := by
    simpa [norm_zpow] using congrArg norm h
  exact zpow_right_injective₀ (by norm_num) (by norm_num) h'

end GlobalTheory.Branching
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSsIdxInjective
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

noncomputable section

namespace GlobalTheory.Branching.SsInj

def ps {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) (a : ℕ) (t : Fin k) : ℕ :=
  ∑ b : Fin r, if b.val < a then m (b, t) else 0

theorem interlaced_iff {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) :
    Interlaced m ↔ ∀ l j : Fin k, j.val = l.val + 1 → ∀ a : Fin r, ps m (a.val + 1) j ≤ ps m a.val l := by
  simp only [Interlaced, InterlacedAt, ps, Finset.sum_filter, zero_add, Nat.lt_succ_iff, Fin.le_def, Fin.lt_def]

theorem ps_zero {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) (t : Fin k) : ps m 0 t = 0 := by simp [ps]

theorem ps_succ {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) (a : Fin r) (t : Fin k) :
    ps m (a.val + 1) t = ps m a.val t + m (a, t) := by
  have : m (a, t) = ∑ b : Fin r, if b = a then m (b, t) else 0 := by simp
  rw [this, ps, ps, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : b = a
  · subst h; simp
  · have h' : b.val ≠ a.val := fun e => h (Fin.ext e)
    rw [if_neg h]
    split_ifs <;> omega

theorem ps_top {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) (t : Fin k) : ps m r t = ∑ b, m (b, t) := by
  simp [ps]

theorem ps_diag {r : ℕ} (m : Fin r × Fin r →₀ ℕ) (hm : Interlaced m) :
    ∀ (t : ℕ) (ht : t < r), ps m t ⟨t, ht⟩ = 0
  | 0, _ => ps_zero m _
  | t + 1, ht => by
    have h1 := (interlaced_iff m).1 hm ⟨t, by omega⟩ ⟨t + 1, ht⟩ rfl ⟨t, by omega⟩
    have h2 := ps_diag m hm t (by omega)
    simp only at h1
    omega

theorem diag_anti {r : ℕ} (m : Fin r × Fin r →₀ ℕ) (hm : Interlaced m) :
    Antitone fun t : Fin r => m (t, t) := by
  cases r with
  | zero => intro a; exact a.elim0
  | succ r =>
    refine Fin.antitone_iff_succ_le.2 fun i => ?_
    have h1 := (interlaced_iff m).1 hm i.castSucc i.succ (by simp) i.succ
    have h2 := ps_succ m i.succ i.succ
    have h3 := ps_succ m i.castSucc i.castSucc
    have h4 : ps m i.succ.val i.succ = 0 := ps_diag m hm _ i.succ.2
    have h5 : ps m i.castSucc.val i.castSucc = 0 := ps_diag m hm _ i.castSucc.2
    simp only [Fin.val_succ, Fin.val_castSucc] at *
    omega

def res {n : ℕ} (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) : Fin n × Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => m (v.1.castSucc, v.2.castSucc)

theorem res_apply {n : ℕ} (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) (a t : Fin n) :
    res m (a, t) = m (a.castSucc, t.castSucc) := rfl

theorem ps_res {n : ℕ} (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) (a : ℕ) (ha : a ≤ n) (t : Fin n) :
    ps (res m) a t = ps m a t.castSucc := by
  have : ¬ n < a := by omega
  simp [ps, Fin.sum_univ_castSucc, res_apply, this]

theorem res_interlaced {n : ℕ} (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) (hm : Interlaced m) :
    Interlaced (res m) := by
  rw [interlaced_iff] at hm ⊢
  intro l j hj a
  rw [ps_res _ _ (by omega), ps_res _ _ (by omega)]
  exact hm l.castSucc j.castSucc hj a.castSucc

def subDiag {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (c : ℕ) : Fin n × Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => m v - if v.1 = v.2 then c else 0

theorem subDiag_add {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (c : ℕ) (hc : ∀ t, c ≤ m (t, t)) (a t : Fin n) :
    subDiag m c (a, t) + (if a = t then c else 0) = m (a, t) := by
  have e : subDiag m c (a, t) = m (a, t) - if a = t then c else 0 := rfl
  rw [e]
  split_ifs with h
  · subst h
    have := hc a
    omega
  · simp

theorem ps_subDiag {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (c : ℕ) (hc : ∀ t, c ≤ m (t, t)) (a : ℕ) (t : Fin n) :
    ps (subDiag m c) a t + (if t.val < a then c else 0) = ps m a t := by
  have : (if t.val < a then c else 0) = ∑ b : Fin n, if b = t then (if t.val < a then c else 0) else 0 := by simp
  rw [this, ps, ps, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have := subDiag_add m c hc b t
  by_cases h : b = t
  · subst h
    simp only [if_true] at this ⊢
    split_ifs <;> omega
  · simp only [if_neg h] at this ⊢
    split_ifs <;> omega

theorem subDiag_interlaced {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (c : ℕ) (hc : ∀ t, c ≤ m (t, t))
    (hm : Interlaced m) : Interlaced (subDiag m c) := by
  rw [interlaced_iff] at hm ⊢
  intro l j hj a
  have h1 := hm l j hj a
  have h2 := ps_subDiag m c hc (a.val + 1) j
  have h3 := ps_subDiag m c hc a.val l
  split_ifs at h2 h3 <;> omega

theorem natW_cast {N : ℕ} (lam : DomWeight N) (t : Fin N) :
    (lam.natW t : ℤ) = lam.w t - lam.detShift := by
  have h0 : 0 < N := t.pos
  have := lam.anti (show t ≤ ⟨N - 1, by omega⟩ from Fin.le_def.2 (by have := t.2; simp only; omega))
  simp only [DomWeight.natW, DomWeight.detShift, dif_pos h0]
  omega

theorem exists_image (n : ℕ) (lam : DomWeight (n + 1)) (m : ssIdx (n + 1) (n + 1) lam.natW) :
    ∃ x : (Σ mu : Below rfl lam, ssIdx n n mu.1.natW),
      (∀ t, x.1.1.w t = lam.detShift + ps m.1 n t.castSucc) ∧
      ∀ a t, x.2.1 (a, t) + (if a = t then (x.1.1.detShift - lam.detShift).toNat else 0) =
        m.1 (a.castSucc, t.castSucc) := by
  obtain ⟨m, hm, hcol⟩ := m
  have hup : ∀ t : Fin n, lam.detShift + ps m n t.castSucc ≤ lam.w t.castSucc := fun t => by
    have h1 := ps_succ m (Fin.last n) t.castSucc
    have h2 := ps_top m t.castSucc
    have h3 := hcol t.castSucc
    have h4 := natW_cast lam t.castSucc
    simp only [Fin.val_last] at h1
    omega
  have hlo : ∀ t : Fin n, lam.w t.succ ≤ lam.detShift + ps m n t.castSucc := fun t => by
    have h1 := (interlaced_iff m).1 hm t.castSucc t.succ (by simp) (Fin.last n)
    have h2 := ps_top m t.succ
    have h3 := hcol t.succ
    have h4 := natW_cast lam t.succ
    simp only [Fin.val_last] at h1
    omega
  let mu : DomWeight n := ⟨fun t => lam.detShift + ps m n t.castSucc, fun i j hij => by
    rcases hij.eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact (hup j).trans ((lam.anti (Fin.le_def.2 (by simpa using hlt))).trans (hlo i))⟩
  have hI : Interlace rfl lam mu := fun i => ⟨hup i, hlo i⟩
  have hr := res_interlaced m hm
  have hc' : ∀ h0 : 0 < n, mu.detShift - lam.detShift =
      (res m (⟨n - 1, by omega⟩, ⟨n - 1, by omega⟩) : ℕ) := fun h0 => by
    have h1 := ps_succ (res m) ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩
    have h2 := ps_diag (res m) hr (n - 1) (by omega)
    have h3 := ps_res m n le_rfl ⟨n - 1, by omega⟩
    have h4 : mu.detShift = lam.detShift + ps m n (Fin.castSucc ⟨n - 1, by omega⟩) := by
      simp only [DomWeight.detShift, dif_pos h0, mu]
    have h5 : n - 1 + 1 = n := by omega
    simp only [h5] at h1
    omega
  have hc : ∀ t, (mu.detShift - lam.detShift).toNat ≤ res m (t, t) := fun t => by
    have h0 : 0 < n := t.pos
    rw [hc' h0, Int.toNat_natCast]
    exact diag_anti _ hr (Fin.le_def.2 (by have := t.2; simp only; omega))
  refine ⟨⟨⟨mu, hI⟩, subDiag (res m) _, subDiag_interlaced _ _ hc hr, fun t => ?_⟩, fun _ => rfl,
    fun a t => subDiag_add _ _ hc a t⟩
  have h1 := ps_subDiag _ _ hc n t
  rw [if_pos t.2, ps_top, ps_res m n le_rfl] at h1
  have h2 := natW_cast mu t
  have h3 : mu.w t = lam.detShift + ps m n t.castSucc := rfl
  have h4 := hc' t.pos
  simp only
  omega

end GlobalTheory.Branching.SsInj

namespace GlobalTheory.Branching

open SsInj

theorem exists_ssIdx_injective : ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N),
    ∃ F : ssIdx N N lam.natW → (Σ mu : Below h lam, ssIdx n n mu.1.natW), Function.Injective F := by
  intro n N h lam
  subst h
  choose F hF1 hF2 using exists_image n lam
  refine ⟨F, fun m m' e => ?_⟩
  have hin : ∀ a t : Fin n, m.1 (a.castSucc, t.castSucc) = m'.1 (a.castSucc, t.castSucc) := fun a t => by
    rw [← hF2 m a t, ← hF2 m' a t, e]
  have hlast : ∀ x : ssIdx (n + 1) (n + 1) lam.natW, ∀ a, x.1 (a, Fin.last n) = 0 := fun x a => by
    have h1 := x.2.2 (Fin.last n)
    have h2 : lam.natW (Fin.last n) = 0 := by
      simp [DomWeight.natW, DomWeight.detShift, Fin.last]
    rw [h2] at h1
    exact Finset.sum_eq_zero_iff.1 h1 a (Finset.mem_univ a)
  apply Subtype.ext
  ext ⟨a, t⟩
  induction t using Fin.lastCases with
  | last => rw [hlast, hlast]
  | cast t =>
    induction a using Fin.lastCases with
    | cast a => exact hin a t
    | last =>
      have h1 := m.2.2 t.castSucc
      have h2 := m'.2.2 t.castSucc
      rw [Fin.sum_univ_castSucc] at h1 h2
      simp only [hin] at h1
      omega

end GlobalTheory.Branching
end
end

