module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.GlobalTheory
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelRowsColumnsSquareIntegrable
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ProperRatH
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ConvTest
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical Pointwise

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

namespace Sum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem kerFin (D : Dom E a b) {φ : H E a b → ℂ} (hφ : IsTestH φ) (x y : H E a b) :
    (Function.support fun γ : ratH E a b => φ (x⁻¹ * (γ : H E a b) * y)).Finite :=
  (E1.kerBasic (E1.ctx E1.ratProper_holds D) φ hφ).1 x y

theorem kerRow (D : Dom E a b) {φ : H E a b → ℂ} (hφ : IsTestH φ) (x : H E a b) :
    MemLp (fun y => kerH φ x y) 2 D.ν :=
  (E1.kernel_rows_columns_square_integrable (E1.ctx E1.ratProper_holds D) φ hφ).2 x

theorem rowI (D : Dom E a b) {φ : H E a b → ℂ} (hφ : IsTestH φ) {f : H E a b → ℂ} (hf : MemLp f 2 D.ν)
    (x : H E a b) : Integrable (fun y => kerH φ x y * f y) D.ν :=
  (kerRow D hφ x).integrable_mul hf

theorem kerAdd (D : Dom E a b) {φ ψ : H E a b → ℂ} (hφ : IsTestH φ) (hψ : IsTestH ψ) (x y : H E a b) :
    kerH (φ + ψ) x y = kerH φ x y + kerH ψ x y := by
  unfold kerH
  exact finsum_add_distrib (kerFin D hφ x y) (kerFin D hψ x y)

theorem kerSmul (D : Dom E a b) {φ : H E a b → ℂ} (hφ : IsTestH φ) (c : ℂ) (x y : H E a b) :
    kerH (c • φ) x y = c * kerH φ x y := by
  unfold kerH
  exact (mul_finsum _ _).symm

theorem testAdd {ι : Type} {Φ Ψ : Matrix ι ι (H E a b → ℂ)} (hΦ : IsTestM Φ) (hΨ : IsTestM Ψ) : IsTestM (Φ + Ψ) :=
  fun i j => ⟨(hΦ i j).1.add (hΨ i j).1, (hΦ i j).2.add (hΨ i j).2⟩

theorem testSmul {ι : Type} {Φ : Matrix ι ι (H E a b → ℂ)} (c : ℂ) (hΦ : IsTestM Φ) : IsTestM (c • Φ) :=
  fun i j => ⟨(hΦ i j).1.const_smul c, (hΦ i j).2.mono (Function.support_const_smul_subset c _)⟩

theorem ropZero (D : Dom E a b) {ι : Type} [Fintype ι] : IsROp D (0 : Matrix ι ι (H E a b → ℂ)) 0 := by
  intro f i
  have e1 : (((0 : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) f i : Lp ℂ 2 D.ν) : H E a b → ℂ) =ᵐ[D.ν] 0 := by
    rw [ContinuousLinearMap.zero_apply, PiLp.zero_apply]
    exact Lp.coeFn_zero _ _ _
  filter_upwards [e1] with x h1
  rw [h1]
  simp [kerH]

theorem ropAdd (D : Dom E a b) {ι : Type} [Fintype ι] {Φ Ψ : Matrix ι ι (H E a b → ℂ)}
    {T S : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D} (hΦ : IsTestM Φ) (hΨ : IsTestM Ψ) (hT : IsROp D Φ T)
    (hS : IsROp D Ψ S) : IsROp D (Φ + Ψ) (T + S) := by
  intro f i
  have e1 : (((T + S) f i : Lp ℂ 2 D.ν) : H E a b → ℂ) =ᵐ[D.ν]
      ((T f i : Lp ℂ 2 D.ν) : H E a b → ℂ) + ((S f i : Lp ℂ 2 D.ν) : H E a b → ℂ) := by
    rw [ContinuousLinearMap.add_apply, PiLp.add_apply]
    exact Lp.coeFn_add _ _
  filter_upwards [e1, hT f i, hS f i] with x h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_add (rowI D (hΦ i j) (Lp.memLp (f j)) x) (rowI D (hΨ i j) (Lp.memLp (f j)) x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Matrix.add_apply, kerAdd D (hΦ i j) (hΨ i j)]
  ring

theorem ropSmul (D : Dom E a b) {ι : Type} [Fintype ι] {Φ : Matrix ι ι (H E a b → ℂ)}
    {T : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D} (c : ℂ) (hΦ : IsTestM Φ) (hT : IsROp D Φ T) :
    IsROp D (c • Φ) (c • T) := by
  intro f i
  have e1 : (((c • T) f i : Lp ℂ 2 D.ν) : H E a b → ℂ) =ᵐ[D.ν] c • ((T f i : Lp ℂ 2 D.ν) : H E a b → ℂ) := by
    rw [ContinuousLinearMap.smul_apply, PiLp.smul_apply]
    exact Lp.coeFn_smul _ _
  filter_upwards [e1, hT f i] with x h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Matrix.smul_apply, kerSmul D (hΦ i j)]
  ring

end Sum

theorem blkSum : BlockLinearCombinations := by
  intro E _ _ _ a b D ι J _ s c Φ T h
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact ⟨fun _ _ => ⟨continuous_const, HasCompactSupport.zero⟩, Sum.ropZero D⟩
  · intro j s hj ih h
    have h' := ih fun k hk => h k (Finset.mem_insert_of_mem hk)
    obtain ⟨h1, h2⟩ := h j (Finset.mem_insert_self j s)
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact ⟨Sum.testAdd (Sum.testSmul (c j) h1) h'.1,
      Sum.ropAdd D (Sum.testSmul (c j) h1) h'.1 (Sum.ropSmul D (c j) h1 h2) h'.2⟩

namespace Sum

section Lev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem hfTop (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) :
    LocallyCompactSpace (Hf E a b) ∧ SecondCountableTopology (Hf E a b) ∧ T2Space (Hf E a b) := by
  obtain ⟨-, ⟨l1, s1, t1⟩, -⟩ := PositivityTheory.Rg.BcB.G8.topo_holds E a
  obtain ⟨-, ⟨l2, s2, t2⟩, -⟩ := PositivityTheory.Rg.BcB.G8.topo_holds E b
  exact ⟨inferInstance, inferInstance, inferInstance⟩

variable [BorelSpace (Hf E a b)] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure] {κ : Type} [Fintype κ]

theorem levLeft {ψ : Matrix κ κ (Hf E a b → ℂ)} (ψ' : Matrix κ κ (Hf E a b → ℂ)) {u : Hf E a b}
    (hu : ∀ x y h, ψ x y (u * h) = ψ x y h) (x y : κ) (g : Hf E a b) :
    mulF ν ψ ψ' x y (u * g) = mulF ν ψ ψ' x y g := by
  unfold mulF
  refine Finset.sum_congr rfl fun z _ => ?_
  refine ((integral_mul_left_eq_self (fun h => ψ x z h * ψ' z y (h⁻¹ * (u * g))) u).symm.trans ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  beta_reduce
  rw [show (u * h)⁻¹ * (u * g) = h⁻¹ * g by group, hu]

theorem levRight (ψ : Matrix κ κ (Hf E a b → ℂ)) {ψ' : Matrix κ κ (Hf E a b → ℂ)} {u : Hf E a b}
    (hu : ∀ x y h, ψ' x y (h * u) = ψ' x y h) (x y : κ) (g : Hf E a b) :
    mulF ν ψ ψ' x y (g * u) = mulF ν ψ ψ' x y g := by
  unfold mulF
  simp only [← mul_assoc, hu]

theorem adjMul (ψ ψ' : Matrix κ κ (Hf E a b → ℂ)) : adjF (mulF ν ψ ψ') = mulF ν (adjF ψ') (adjF ψ) := by
  funext x y g
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [adjF, mulF, map_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← integral_conj]
  refine Eq.trans ?_ (integral_mul_left_eq_self
    (fun h => starRingEnd ℂ (ψ' z x h⁻¹) * starRingEnd ℂ (ψ y z (h⁻¹ * g)⁻¹)) g)
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  have e1 : ((g * h)⁻¹ * g)⁻¹ = h := by group
  have e2 : (g * h)⁻¹ = h⁻¹ * g⁻¹ := by group
  simp only [e1]
  simp only [e2, map_mul]
  ring

theorem convTest {A B' : Hf E a b → ℂ} (hA : Continuous A ∧ HasCompactSupport A)
    (hB : Continuous B' ∧ HasCompactSupport B') :
    Continuous (fun h => ∫ k, A k * B' (k⁻¹ * h) ∂ν) ∧ HasCompactSupport (fun h => ∫ k, A k * B' (k⁻¹ * h) ∂ν) := by
  have := PMul.mulF_fin (κ := Unit) ν (ψ := fun _ _ => A) (ψ' := fun _ _ => B') (fun _ _ => hA) (fun _ _ => hB) () ()
  unfold mulF at this
  simpa using this

variable [LocallyCompactSpace (Hf E a b)] [SecondCountableTopology (Hf E a b)] [T2Space (Hf E a b)]

theorem assoc1 {A B' C : Hf E a b → ℂ} (hA : Continuous A ∧ HasCompactSupport A)
    (hB : Continuous B' ∧ HasCompactSupport B') (hC : Continuous C ∧ HasCompactSupport C) (g : Hf E a b) :
    ∫ h, (∫ k, A k * B' (k⁻¹ * h) ∂ν) * C (h⁻¹ * g) ∂ν = ∫ k, A k * ∫ h, B' h * C (h⁻¹ * (k⁻¹ * g)) ∂ν ∂ν := by
  have inner : ∀ k, ∫ h, B' h * C (h⁻¹ * (k⁻¹ * g)) ∂ν = ∫ h, B' (k⁻¹ * h) * C (h⁻¹ * g) ∂ν := by
    intro k
    calc ∫ h, B' h * C (h⁻¹ * (k⁻¹ * g)) ∂ν
        = ∫ h, B' (k⁻¹ * h) * C ((k⁻¹ * h)⁻¹ * (k⁻¹ * g)) ∂ν :=
          (integral_mul_left_eq_self (fun h => B' h * C (h⁻¹ * (k⁻¹ * g))) k⁻¹).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun h => by
          beta_reduce; rw [show (k⁻¹ * h)⁻¹ * (k⁻¹ * g) = h⁻¹ * g by group])
  have lhs : ∀ h, (∫ k, A k * B' (k⁻¹ * h) ∂ν) * C (h⁻¹ * g) = ∫ k, A k * B' (k⁻¹ * h) * C (h⁻¹ * g) ∂ν :=
    fun h => (integral_mul_const _ _).symm
  have rhs : ∀ k, A k * ∫ h, B' (k⁻¹ * h) * C (h⁻¹ * g) ∂ν = ∫ h, A k * B' (k⁻¹ * h) * C (h⁻¹ * g) ∂ν :=
    fun k => by rw [← integral_const_mul]; simp only [mul_assoc]
  simp_rw [lhs, inner, rhs]
  have hcont : Continuous fun p : Hf E a b × Hf E a b => A p.2 * B' (p.2⁻¹ * p.1) * C (p.1⁻¹ * g) :=
    ((hA.1.comp continuous_snd).mul (hB.1.comp (continuous_snd.inv.mul continuous_fst))).mul
      (hC.1.comp (continuous_fst.inv.mul continuous_const))
  have hK : IsCompact ((tsupport A * tsupport B') ×ˢ tsupport A) :=
    (hA.2.isCompact.mul hB.2.isCompact).prod hA.2.isCompact
  set_option synthInstance.maxHeartbeats 100000 in
    refine integral_integral_swap (f := fun h k => A k * B' (k⁻¹ * h) * C (h⁻¹ * g)) ?_
  set_option synthInstance.maxHeartbeats 100000 in
    refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hK fun p hp => ?_)
  by_contra hne
  have h1 : A p.2 ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have h2 : B' (p.2⁻¹ * p.1) ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
  exact hp ⟨Set.mem_mul.2 ⟨p.2, subset_tsupport _ h1, p.2⁻¹ * p.1, subset_tsupport _ h2, mul_inv_cancel_left _ _⟩,
    subset_tsupport _ h1⟩

theorem assoc {ψ ψ' ψ'' : Matrix κ κ (Hf E a b → ℂ)} (h1 : IsFinM ψ) (h2 : IsFinM ψ') (h3 : IsFinM ψ'') :
    mulF ν (mulF ν ψ ψ') ψ'' = mulF ν ψ (mulF ν ψ' ψ'') := by
  funext x y g
  simp only [mulF]
  have L : ∀ w, ∫ h, (∑ z, ∫ k, ψ x z k * ψ' z w (k⁻¹ * h) ∂ν) * ψ'' w y (h⁻¹ * g) ∂ν =
      ∑ z, ∫ h, (∫ k, ψ x z k * ψ' z w (k⁻¹ * h) ∂ν) * ψ'' w y (h⁻¹ * g) ∂ν := by
    intro w
    simp_rw [Finset.sum_mul]
    refine integral_finsetSum _ fun z _ => ?_
    obtain ⟨c1, c2⟩ := convTest ν (h1 x z) (h2 z w)
    exact (c1.mul ((h3 w y).1.comp (continuous_inv.mul continuous_const))).integrable_of_hasCompactSupport c2.mul_right
  have R : ∀ z, ∫ k, ψ x z k * (∑ w, ∫ h, ψ' z w h * ψ'' w y (h⁻¹ * (k⁻¹ * g)) ∂ν) ∂ν =
      ∑ w, ∫ k, ψ x z k * ∫ h, ψ' z w h * ψ'' w y (h⁻¹ * (k⁻¹ * g)) ∂ν ∂ν := by
    intro z
    simp_rw [Finset.mul_sum]
    refine integral_finsetSum _ fun w _ => ?_
    obtain ⟨c1, -⟩ := convTest ν (h2 z w) (h3 w y)
    have c3 : Continuous fun k : Hf E a b => ∫ h, ψ' z w h * ψ'' w y (h⁻¹ * (k⁻¹ * g)) ∂ν :=
      c1.comp (continuous_inv.mul continuous_const)
    exact ((h1 x z).1.mul c3).integrable_of_hasCompactSupport (h1 x z).2.mul_right
  refine (Finset.sum_congr rfl fun w _ => L w).trans (Eq.trans ?_ (Finset.sum_congr rfl fun z _ => R z).symm)
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => assoc1 ν (h1 x z) (h2 z w) (h3 w y) g

end Lev

end Sum

theorem blkLevel : BlockProductLevels := by
  intro E _ _ _ B ψ ψ' ψ'' h1 h2 h3
  haveI := B.hν
  haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  obtain ⟨_, _, _⟩ := Sum.hfTop E B.a B.b
  exact ⟨fun u hu x y g => Sum.levLeft B.ν ψ' hu x y g, fun u hu x y g => Sum.levRight B.ν ψ hu x y g,
    Sum.assoc B.ν h1 h2 h3, Sum.adjMul B.ν ψ ψ'⟩

end PositivityTheory.Rg.BcB.F

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.LogSizeInv
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

namespace Op

theorem bsG (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩

theorem bsF (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : BorelSpace (Hf E a b) := ⟨rfl⟩

attribute [local instance] bsG bsF

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem logSize_inv {n : ℕ} (g : GA E n) : logSize g⁻¹ = logSize g := by
  rw [logSize, logSize, inv_inv, add_comm]

theorem adjVal_spec (h2 : MultAlg) {n : ℕ} (μ : Measure (G n)) [μ.IsHaarMeasure] {M : Mods E n} (k : Kers M)
    (val : InfinitePlace E → Inf n → ℂ) (T : ℝ) (v : InfinitePlace E) (hk : IsMult μ (M v) (k v) (val v) T) :
    IsMult μ (M v) (adjK k v) (adjVal μ k val T v) T ∧
      ∀ χ, IsHerm χ → adjVal μ k val T v χ = starRingEnd ℂ (val v χ) := by
  have hex : ∃ val₁, IsMult μ (M v) (adjK k v) val₁ T ∧ ∀ χ, IsHerm χ → val₁ χ = starRingEnd ℂ (val v χ) := by
    obtain ⟨-, -, h, -⟩ := h2 n μ (M v) (k v) (k v) (val v) (val v) T T hk hk
    exact h
  have e : adjVal μ k val T v = hex.choose := dif_pos hex
  rw [e]
  exact hex.choose_spec

variable (B : Block E)

theorem opOf_eq (h1 : OpEx) {Φ : Matrix B.I B.I (H E B.a B.b → ℂ)} {T : B.Hb →L[ℂ] B.Hb} (hΦ : IsTestM Φ)
    (hT : IsROp B.D Φ T) : B.opOf Φ = T := by
  have hex : ∃ T, IsROp B.D Φ T := ⟨T, hT⟩
  have e : B.opOf Φ = hex.choose := dif_pos hex
  rw [e]
  exact ((h1 E B.a B.b B.D B.I).1 Φ hΦ).unique hex.choose_spec hT

theorem test (h3 : TensTest) (t : PT B) (ht : t.Ok) : IsTestM t.Φ := by
  haveI := B.ha; haveI := B.hb
  exact (h3 E B.a B.b B.μa B.μb B.Ma B.Mb B.κ t.ka t.kb t.va t.vb t.T t.ψ ht.ka ht.kb ht.ψ).1

theorem rop (h1 : OpEx) (h3 : TensTest) (t : PT B) (ht : t.Ok) : IsROp B.D t.Φ t.op := by
  have hex := ((h1 E B.a B.b B.D B.I).1 t.Φ (test B h3 t ht)).exists
  have e : B.opOf t.Φ = hex.choose := dif_pos hex
  show IsROp B.D t.Φ (B.opOf t.Φ)
  rw [e]
  exact hex.choose_spec

theorem mulOk (h2 : MultAlg) (h4 : TensMul) (t t' : PT B) (ht : t.Ok) (ht' : t'.Ok) : (t.mul t').Ok := by
  haveI := B.ha; haveI := B.hb; haveI := B.hν
  refine ⟨add_nonneg ht.T ht'.T, add_nonneg (add_nonneg ht.r ht'.r) B.c_nonneg, fun v => ?_, fun v => ?_, ?_, ?_⟩
  · exact (h2 B.a B.μa (B.Ma v) (t.ka v) (t'.ka v) (t.va v) (t'.va v) t.T t'.T (ht.ka v) (ht'.ka v)).1
  · exact (h2 B.b B.μb (B.Mb v) (t.kb v) (t'.kb v) (t.vb v) (t'.vb v) t.T t'.T (ht.kb v) (ht'.kb v)).1
  · exact (h4 E B.a B.b B.D B.μa B.μb B.ν B.Ma B.Mb B.κ t.ka t'.ka t.kb t'.kb t.va t'.va t.vb t'.vb t.T t'.T t.ψ t'.ψ
      B.compat ht.ka ht.kb ht'.ka ht'.kb ht.ψ ht'.ψ).1
  · intro x y g hg
    have hg' : ∑ z, ∫ h, t.ψ x z h * t'.ψ z y (h⁻¹ * g) ∂B.ν ≠ 0 := hg
    obtain ⟨z, hz⟩ : ∃ z, ∫ h, t.ψ x z h * t'.ψ z y (h⁻¹ * g) ∂B.ν ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hg' (Finset.sum_eq_zero fun z _ => hc z)
    obtain ⟨h, hh⟩ : ∃ h, t.ψ x z h * t'.ψ z y (h⁻¹ * g) ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hz (by simp [hc])
    have s1 := ht.size x z h (left_ne_zero_of_mul hh)
    have s2 := ht'.size z y (h⁻¹ * g) (right_ne_zero_of_mul hh)
    have e1 : g.1 = h.1 * (h⁻¹ * g).1 := by rw [← Prod.fst_mul, mul_inv_cancel_left]
    have e2 : g.2 = h.2 * (h⁻¹ * g).2 := by rw [← Prod.snd_mul, mul_inv_cancel_left]
    show logSize (finGL E B.a g.1) ≤ t.r + t'.r + B.c ∧ logSize (finGL E B.b g.2) ≤ t.r + t'.r + B.c
    rw [e1, e2, map_mul, map_mul]
    constructor
    · linarith [B.ca (finGL E B.a h.1) (finGL E B.a (h⁻¹ * g).1), s1.1, s2.1]
    · linarith [B.cb (finGL E B.b h.2) (finGL E B.b (h⁻¹ * g).2), s1.2, s2.2]

theorem mulOp (h1 : OpEx) (h3 : TensTest) (h4 : TensMul) (t t' : PT B) (ht : t.Ok) (ht' : t'.Ok) :
    (t.mul t').op = t.op * t'.op := by
  haveI := B.ha; haveI := B.hb; haveI := B.hν
  have hm := h4 E B.a B.b B.D B.μa B.μb B.ν B.Ma B.Mb B.κ t.ka t'.ka t.kb t'.kb t.va t'.va t.vb t'.vb t.T t'.T t.ψ t'.ψ
      B.compat ht.ka ht.kb ht'.ka ht'.kb ht.ψ ht'.ψ
  have hΦ : (t.mul t').Φ = mulM B.D.μ t.Φ t'.Φ := hm.2.symm
  have h := (h1 E B.a B.b B.D B.I).2 t.Φ t'.Φ t.op t'.op (test B h3 t ht) (test B h3 t' ht') (rop B h1 h3 t ht)
    (rop B h1 h3 t' ht')
  show B.opOf (t.mul t').Φ = _
  rw [hΦ]
  exact opOf_eq B h1 h.1 h.2.1

theorem adjOk (h2 : MultAlg) (t : PT B) (ht : t.Ok) : t.adj.Ok := by
  haveI := B.ha; haveI := B.hb
  refine ⟨ht.T, ht.r, fun v => (adjVal_spec h2 B.μa t.ka t.va t.T v (ht.ka v)).1,
    fun v => (adjVal_spec h2 B.μb t.kb t.vb t.T v (ht.kb v)).1, fun x y => ⟨?_, ?_⟩, ?_⟩
  · exact Complex.continuous_conj.comp ((ht.ψ y x).1.comp continuous_inv)
  · exact ((ht.ψ y x).2.comp_homeomorph (Homeomorph.inv _)).comp_left (g := starRingEnd ℂ) (map_zero _)
  · intro x y g hg
    have hg' : t.ψ y x g⁻¹ ≠ 0 := fun h0 => hg (by show starRingEnd ℂ (t.ψ y x g⁻¹) = 0; rw [h0, map_zero])
    have s := ht.size y x g⁻¹ hg'
    rw [Prod.fst_inv, Prod.snd_inv, map_inv, map_inv, logSize_inv, logSize_inv] at s
    exact s

theorem adjOp (h1 : OpEx) (h2 : MultAlg) (h3 : TensTest) (t : PT B) (ht : t.Ok) :
    t.adj.op = ContinuousLinearMap.adjoint t.op := by
  haveI := B.ha; haveI := B.hb
  have ha := h3 E B.a B.b B.μa B.μb B.Ma B.Mb B.κ t.ka t.kb t.va t.vb t.T t.ψ ht.ka ht.kb ht.ψ
  have hΦ : t.adj.Φ = adjM t.Φ := ha.2.symm
  have h := (h1 E B.a B.b B.D B.I).2 t.Φ t.Φ t.op t.op (test B h3 t ht) (test B h3 t ht) (rop B h1 h3 t ht)
    (rop B h1 h3 t ht)
  have htest : IsTestM (adjM t.Φ) := hΦ ▸ test B h3 t.adj (adjOk B h2 t ht)
  show B.opOf t.adj.Φ = _
  rw [hΦ]
  exact opOf_eq B h1 htest h.2.2

theorem mulVal (t t' : PT B) (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b) :
    (t.mul t').val χa χb = t.val χa χb * t'.val χa χb := by
  simp only [PT.val, PT.mul, valA, Pi.mul_apply, Finset.prod_mul_distrib]
  ring

theorem adjValEq (h2 : MultAlg) (t : PT B) (ht : t.Ok) (χa : InfinitePlace E → Inf B.a)
    (χb : InfinitePlace E → Inf B.b) (ha : ∀ v, IsHerm (χa v)) (hb : ∀ v, IsHerm (χb v)) :
    t.adj.val χa χb = starRingEnd ℂ (t.val χa χb) := by
  haveI := B.ha; haveI := B.hb
  simp only [PT.val, PT.adj, valA]
  rw [map_mul, map_prod, map_prod]
  congr 1
  · exact Finset.prod_congr rfl fun v _ => (adjVal_spec h2 B.μa t.ka t.va t.T v (ht.ka v)).2 _ (ha v)
  · exact Finset.prod_congr rfl fun v _ => (adjVal_spec h2 B.μb t.kb t.vb t.T v (ht.kb v)).2 _ (hb v)

theorem commPhi (h2 : MultAlg) (t t' : PT B) (ht : t.Ok) (ht' : t'.Ok)
    (hψ : mulF B.ν t.ψ t'.ψ = mulF B.ν t'.ψ t.ψ) : (t.mul t').Φ = (t'.mul t).Φ := by
  haveI := B.ha; haveI := B.hb
  have ea : ∀ v (g : GA E B.a), convK B.μa t.ka t'.ka v (gInf v g).val = convK B.μa t'.ka t.ka v (gInf v g).val :=
    fun v g => (h2 B.a B.μa (B.Ma v) (t.ka v) (t'.ka v) (t.va v) (t'.va v) t.T t'.T (ht.ka v) (ht'.ka v)).2.1 _
      (Matrix.isUnits_det_units _).ne_zero
  have eb : ∀ v (g : GA E B.b), convK B.μb t.kb t'.kb v (gInf v g).val = convK B.μb t'.kb t.kb v (gInf v g).val :=
    fun v g => (h2 B.b B.μb (B.Mb v) (t.kb v) (t'.kb v) (t.vb v) (t'.vb v) t.T t'.T (ht.kb v) (ht'.kb v)).2.1 _
      (Matrix.isUnits_det_units _).ne_zero
  funext i j g
  simp only [PT.Φ, PT.mul, tens, entA, hψ, ea, eb]

end Op

theorem blkOp (h1 : OpEx) (h2 : MultAlg) (h3 : TensTest) (h4 : TensMul) : BlockOperatorsProductAdjoint := by
  intro E _ _ _ B t t' ht ht'
  exact ⟨Op.test B h3 t ht, Op.rop B h1 h3 t ht, Op.mulOk B h2 h4 t t' ht ht', Op.mulOp B h1 h3 h4 t t' ht ht',
    Op.adjOk B h2 t ht, Op.adjOp B h1 h2 h3 t ht, Op.mulVal B t t', Op.adjValEq B h2 t ht⟩

theorem blkComm (h1 : OpEx) (h2 : MultAlg) (h3 : TensTest) (h4 : TensMul) : BlockPureTensorsCommute := by
  intro E _ _ _ B t t' ht ht' hψ
  show t.op * t'.op = t'.op * t.op
  rw [← Op.mulOp B h1 h3 h4 t t' ht ht', ← Op.mulOp B h1 h3 h4 t' t ht' ht]
  exact congrArg B.opOf (Op.commPhi B h2 t t' ht ht' hψ)

end PositivityTheory.Rg.BcB.F

end
end

