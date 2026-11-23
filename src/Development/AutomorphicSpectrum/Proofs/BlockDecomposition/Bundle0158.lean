module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0133
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0150
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0155
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0152
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0154

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinrankChartLatQMono
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.ChartSections

theorem finrank_chartLatQ_mono : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (b b' : K → ℤ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → b ≤ b' →
    FiniteDimensional ℚ (chartLatQ y b' 1) →
    Module.finrank ℚ (chartLatQ y b 1) ≤ Module.finrank ℚ (chartLatQ y b' 1) := by
  intro K _ ι _ Ω _ _ y b b' hy hb hfd
  choose j hj using hy
  obtain ⟨n, hn⟩ : ∃ n : K → ℕ, ∀ k, (n k : ℤ) = b' k - b k :=
    ⟨fun k => (b' k - b k).toNat, fun k => Int.toNat_of_nonneg (sub_nonneg.2 (hb k))⟩
  have hu0 : (∏ k, y ⟨k, j k⟩ ^ n k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hj k)
  have hmem : ∀ s ∈ chartLatQ y b 1, s * ∏ k, y ⟨k, j k⟩ ^ n k ∈ chartLatQ y b' 1 := by
    intro s hs c hc
    have h1 : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) ∈ chartRingQ y c := hs c hc
    have hq : ∀ k, y ⟨k, j k⟩ / y ⟨k, c k⟩ ∈ chartRingQ y c :=
      fun k => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩
    have h2 : ∏ k, (y ⟨k, j k⟩ / y ⟨k, c k⟩) ^ n k ∈ chartRingQ y c :=
      prod_mem fun k _ => pow_mem (hq k) _
    have heq : s * (∏ k, y ⟨k, j k⟩ ^ n k) * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b' k)) =
        (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k))) * ∏ k, (y ⟨k, j k⟩ / y ⟨k, c k⟩) ^ n k := by
      rw [mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      have hck := hc k
      have hnk := hn k
      have hz : y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b' k)) =
          y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) * (y ⟨k, c k⟩ ^ n k)⁻¹ := by
        rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ hck]
        congr 1
        simp only [Nat.cast_one, one_mul]
        omega
      rw [hz, div_pow, div_eq_mul_inv]
      ring
    show s * (∏ k, y ⟨k, j k⟩ ^ n k) * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b' k)) ∈ chartRingQ y c
    rw [heq]
    exact mul_mem h1 h2
  let f : chartLatQ y b 1 →ₗ[ℚ] chartLatQ y b' 1 :=
    { toFun := fun s => ⟨s.1 * ∏ k, y ⟨k, j k⟩ ^ n k, hmem s.1 s.2⟩
      map_add' := fun s t => Subtype.ext (add_mul _ _ _)
      map_smul' := fun r s => Subtype.ext (smul_mul_assoc _ _ _) }
  refine LinearMap.finrank_le_finrank_of_injective (f := f) fun s t hst => ?_
  exact Subtype.ext (mul_right_cancel₀ hu0 (congrArg Subtype.val hst))

end GlobalTheory.CompanionTheory.ChartSections
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomology
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

universe w v u w' v' u'

namespace GlobalTheory.CompanionTheory.CosieveBC

open GlobalTheory.CompanionTheory.CosieveMV

section Cover

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u} [Category.{v} C]
  {C' : Type u'} [Category.{v'} C'] {G : C' ⥤ C} {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)] {F : ι → (C ⥤ ModuleCat.{w} R)} {F' : C' ⥤ ModuleCat.{w'} R'}
  {τ : ∀ i, N i → ∀ T : C', (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T}
  {hτ : ∀ i n {T T' : C'} (φ : T ⟶ T') x, τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x)}

theorem subsingleton_H {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    {W : ObjectProperty C} (h : ∀ T, ¬ W T) (j : ℕ) : Subsingleton ((cw F W).H j) := by
  have : Subsingleton ((cw F W).X j) := ⟨fun _ _ => funext fun s => (h _ (s.obj 0).property).elim⟩
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
  refine (CrystallineSemistableComparison.CechClassBoundaries.cls_eq_zero a ha).2 ?_
  rw [Subsingleton.elim a 0]
  exact zero_mem _

theorem bc_congr [DecidableEq ι] {W W₂ : ObjectProperty C} {W' W₂' : ObjectProperty C'} (e : ∀ T, W T ↔ W₂ T)
    (e' : ∀ T, W' T ↔ W₂' T) (h : ∀ T, W' T → W (G.obj T)) (h₂ : ∀ T, W₂' T → W₂ (G.obj T))
    (t : BC (Phi G F F' τ hτ h)) : BC (Phi G F F' τ hτ h₂) := by
  obtain rfl : W = W₂ := funext fun T => propext (e T)
  obtain rfl : W' = W₂' := funext fun T => propext (e' T)
  exact t

theorem Wc_insert {α : Type} [DecidableEq α] {D : Type u} [Category.{v} D] (U : α → ObjectProperty D) (a : α)
    (A S : Finset α) (T : D) : supP (Wc U A S) (capS U (insert a S)) T ↔ Wc U (insert a A) S T := by
  constructor
  · rintro (⟨⟨b, hb, hT⟩, hS⟩ | h)
    · exact ⟨⟨b, Finset.mem_insert_of_mem hb, hT⟩, hS⟩
    · exact ⟨⟨a, Finset.mem_insert_self _ _, h a (Finset.mem_insert_self _ _)⟩,
        fun b hb => h b (Finset.mem_insert_of_mem hb)⟩
  · rintro ⟨⟨b, hb, hT⟩, hS⟩
    rcases Finset.mem_insert.1 hb with rfl | h
    · refine Or.inr fun c hc => ?_
      rcases Finset.mem_insert.1 hc with rfl | h'
      · exact hT
      · exact hS c h'
    · exact Or.inl ⟨⟨b, h, hT⟩, hS⟩

theorem Wc_inf {α : Type} [DecidableEq α] {D : Type u} [Category.{v} D] (U : α → ObjectProperty D) (a : α)
    (A S : Finset α) (T : D) : Wc U A (insert a S) T ↔ infP (Wc U A S) (capS U (insert a S)) T :=
  ⟨fun h => ⟨⟨h.1, fun b hb => h.2 b (Finset.mem_insert_of_mem hb)⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩

theorem wc_le {α : Type} {U : α → ObjectProperty C} {U' : α → ObjectProperty C'}
    (h : ∀ a T, U' a T → U a (G.obj T)) (A S : Finset α) (T : C') (hT : Wc U' A S T) : Wc U A S (G.obj T) := by
  obtain ⟨⟨a, ha, hT⟩, hS⟩ := hT
  exact ⟨⟨a, ha, h a T hT⟩, fun b hb => h b T (hS b hb)⟩

theorem cap_le {α : Type} {U : α → ObjectProperty C} {U' : α → ObjectProperty C'}
    (h : ∀ a T, U' a T → U a (G.obj T)) (S : Finset α) (T : C') (hT : capS U' S T) : capS U S (G.obj T) :=
  fun b hb => h b T (hT b hb)

theorem bc_Wc [Fintype ι] [DecidableEq ι] [∀ i, Module.Flat R (N i)] {α : Type} [DecidableEq α]
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x)
    (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x)
    {U : α → ObjectProperty C} {U' : α → ObjectProperty C'} (hU : ∀ a, Cosieve (U a)) (hU' : ∀ a, Cosieve (U' a))
    (h : ∀ a T, U' a T → U a (G.obj T))
    (hcap : ∀ S : Finset α, S.Nonempty → BC (Phi G F F' τ hτ (cap_le h S))) (A : Finset α) :
    ∀ S : Finset α, BC (Phi G F F' τ hτ (wc_le h A S)) := by
  induction A using Finset.induction_on with
  | empty =>
    intro S j
    have e : ∀ {D : Type u} [Category.{v} D] (P : α → ObjectProperty D) (T : D), ¬ Wc P ∅ S T := by
      intro D _ P T hT
      simpa using hT.1
    have e' : ∀ {D : Type u'} [Category.{v'} D] (P : α → ObjectProperty D) (T : D), ¬ Wc P ∅ S T := by
      intro D _ P T hT
      simpa using hT.1
    have s1 := fun i => subsingleton_H (F i) (e U) j
    have s2 := subsingleton_H F' (e' U') j
    exact tens_subsingleton _
  | insert a A ha ih =>
    intro S
    have key := bc_sup (G := G) (F := F) (F' := F') (τ := τ) (hτ := hτ) hadd hsm (cosieve_Wc hU A S)
      (cosieve_capS hU (insert a S)) (cosieve_Wc hU' A S) (cosieve_capS hU' (insert a S))
      (wc_le h A S) (cap_le h (insert a S)) (ih S) (hcap _ (Finset.insert_nonempty _ _))
      (bc_congr (Wc_inf U a A S) (Wc_inf U' a A S) _ _ (ih (insert a S)))
    exact bc_congr (Wc_insert U a A S) (Wc_insert U' a A S) _ _ key

theorem restrict_bij {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    {W : ObjectProperty C} (hall : ∀ T, W T) (n : ℕ) :
    Function.Bijective ((CH.Mor.restrict F W.ι).hom.f n) := by
  have hW : Cosieve W := fun _ _ _ _ => hall _
  refine ⟨fun x y hxy => funext fun s => congrFun hxy (liftCh hW s (hall _)), fun y => ⟨extZ hW y, pull_extZ hW y⟩⟩

def resEquiv {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    {W : ObjectProperty C} (hall : ∀ T, W T) (j : ℕ) : CH.H F j ≃ₗ[R] (cw F W).H j :=
  LinearEquiv.ofBijective ((CH.Mor.restrict F W.ι).hom.mapH j) (CrystallineSemistableComparison.P.mapH_bij _ (restrict_bij F hall) j)

theorem tens_top [Fintype ι] [DecidableEq ι]
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x)
    (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x)
    {W : ObjectProperty C} {W' : ObjectProperty C'} (hall : ∀ T, W T) (hall' : ∀ T, W' T)
    (h : ∀ T, W' T → W (G.obj T)) (t : BC (Phi G F F' τ hτ h)) (j : ℕ) :
    Tens R (N := N) (M := fun i => CH.H (F i) j) (M' := CH.H F' j)
      fun i n x => (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ).pull j x := by
  have lq : Lin (K := fun i => CH.cx (F i)) (K' := CH.cx F') (σ := σ)
      fun i n => (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ).hom :=
    ⟨fun i n n' k x => funext fun s => hadd i n n' _ _, fun i r n k x => funext fun s => hsm i r n _ _⟩
  refine tens_of_bij (bal_mapH (phi_lin hadd hsm h) j) (bal_mapH lq j) (fun i => resEquiv (F i) hall j)
    (resEquiv F' hall' j).toAddEquiv (fun i n x => ?_) (t j)
  obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
  rfl

end Cover

theorem base_change_of_cover : ∀ {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    (G : C' ⥤ C) {ι : Type} [Fintype ι] [DecidableEq ι] (N : ι → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, Module.Flat R (N i)] (F : ι → (C ⥤ ModuleCat.{0} R)) (F' : C' ⥤ ModuleCat.{0} R')
    (τ : ∀ i, N i → ∀ T : C', (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T) (hτ : ∀ i n {T T' : C'} (φ : T ⟶ T') x,
      τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x))
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x) (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x)
    {A : Type} [Fintype A] (U : A → ObjectProperty C) (U' : A → ObjectProperty C') (hU : ∀ α, Cosieve (U α))
    (hU' : ∀ α, Cosieve (U' α)) (hc : ∀ T, ∃ α, U α T) (hc' : ∀ T, ∃ α, U' α T) (h : ∀ α T, U' α T → U α (G.obj T)),
    (∀ S : Finset A, S.Nonempty → ∀ j, Tens R (N := N) (M := fun i => HU (F i) (capS U S) j) (M' := HU F' (capS U' S) j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) (U := capS U S) (U' := capS U' S)
        fun T hT α hα => h α T (hT α hα)).pull j x) →
    ∀ j, Tens R (N := N) (M := fun i => CH.H (F i) j) (M' := CH.H F' j)
      fun i n x => (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ).pull j x := by
  intro R R' _ _ σ C C' _ _ G ι _ _ N _ _ _ F F' τ hτ hadd hsm A _ U U' hU hU' hc hc' h H j
  classical
  have key := bc_Wc (G := G) (F := F) (F' := F') (τ := τ) (hτ := hτ) hadd hsm hU hU' h
    (fun S hS j => H S hS j) Finset.univ ∅
  refine tens_top hadd hsm (W := Wc U Finset.univ ∅) (W' := Wc U' Finset.univ ∅) (fun T => ?_) (fun T => ?_) _ key j
  · obtain ⟨a, ha⟩ := hc T
    exact ⟨⟨a, Finset.mem_univ _, ha⟩, fun b hb => by simp at hb⟩
  · obtain ⟨a, ha⟩ := hc' T
    exact ⟨⟨a, Finset.mem_univ _, ha⟩, fun b hb => by simp at hb⟩

end GlobalTheory.CompanionTheory.CosieveBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormRespectsFiltrationStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_form_respects_filtration : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil)
    {d : ℕ} (E : Frame (Φ := Φ) d) (σ : ∀ T : C, E.D ⟶ T) (j q : ℕ) (I : Fin j → Fin d) (x : Φ.A.obj E.D), x ∈ (Fil q).S E.D →
    ∀ s : ComposableArrows C j, E.form σ I x s ∈ (Fil ((j + q : ℕ) : ℤ)).S (s.obj (Fin.last j)) := by
  intro R _ C _ Φ Fil hF d E σ j q I x hx s
  have prod_fil_mem (T : C) (n : ℕ) (f : Fin n → Φ.A.obj T)
      (hf : ∀ k, f k ∈ (Fil 1).S T) : ∏ k, f k ∈ (Fil (n : ℤ)).S T := by
    induction n with
    | zero =>
      rw [hF.top ((0 : ℕ) : ℤ) (by simp) T]
      exact Submodule.mem_top
    | succ n ih =>
      rw [Fin.prod_univ_succ]
      simpa only [Nat.add_comm 1 n] using
        hF.mul 1 n T (hf 0) (ih (fun k => f k.succ) fun k => hf k.succ)
  refine hF.mul j q _ (prod_fil_mem _ j _ fun k => (Fil 1).map_mem _ ?_) ((Fil q).map_mem (σ _) hx)
  rw [hF.one]
  exact E.mem _ _ _
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctorialityOfPeriodRingMaps
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PAlgNat

variable {l : ℕ} [Fact l.Prime]

theorem mapAcris_acrisOfTilt {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    mapAcr f 1 (A.aTo1 a) = B.aTo1 (Hom.f f a) := by
  have h := A.aTo1_coeff (WittVector.teichmuller l a)
  rw [WittVector.teichmuller_coeff_zero] at h
  have h' := B.aTo1_coeff (WittVector.teichmuller l (Hom.f f a))
  rw [WittVector.teichmuller_coeff_zero] at h'
  rw [h, h', mapAcr_toAcr, mapW, WittVector.map_teichmuller]

theorem mapAcr_expand {A B : PAlg l} (f : A ⟶ B) (c : ℕ →₀ A.A) :
    mapAcr f 1 (A.expand c) = B.expand (c.mapRange (Hom.f f) (map_zero _)) := by
  rw [expand, expand, map_finsuppSum, Finsupp.sum_mapRange_index (fun k => by simp)]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [map_mul, mapAcris_acrisOfTilt, mapAcr_dxi]

theorem mapU_sharp {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    mapU f (A.sharp a) = B.sharp (Hom.f f a) := by
  change mapU f (A.th (WittVector.teichmuller l a)) = B.th (WittVector.teichmuller l (Hom.f f a))
  rw [mapU_th, mapW, WittVector.map_teichmuller]

theorem mapUnits_unitsOfTilt {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    mapUn f 1 (A.aToU1 a) = B.aToU1 (Hom.f f a) := by
  rw [sharpMap_eq, sharpMap_eq, ← mapU_sharp]
  rfl

theorem mk_mapAcr_toAcr {A B : PAlg l} (f : A ⟶ B) (n : ℕ) (x : A.W) :
    Ideal.Quotient.mk (B.Fil n 1) (mapAcr f n (A.toAcr n x)) = B.uToQ n (mapU f (A.th x)) := by
  rw [mapAcr_toAcr, mapU_th, uToQ_th]

theorem algebraMap_eq_acrisOfTilt (A : PAlg l) (x : Ainf l) :
    algebraMap (Ainf l) (A.Acr 1) x = A.aTo1 (A.s (x.coeff 0)) := by
  have h := A.aTo1_coeff (A.sW x)
  have e : (A.sW x).coeff 0 = A.s (x.coeff 0) := WittVector.map_coeff _ _ _
  rw [e] at h
  rw [h]
  rfl

theorem expand_nat {l : ℕ} [Fact l.Prime] (A : PAlg l) (B : PAlg l) (f : A ⟶ B) :
    (∀ a, mapAcr f 1 (A.aTo1 a) = B.aTo1 (Hom.f f a)) ∧
    (∀ c : ℕ →₀ A.A, mapAcr f 1 (A.expand c) = B.expand (c.mapRange (Hom.f f) (map_zero _))) ∧
    (∀ a, mapU f (A.sharp a) = B.sharp (Hom.f f a)) ∧
    (∀ a, mapUn f 1 (A.aToU1 a) = B.aToU1 (Hom.f f a)) ∧
    (∀ n x, Ideal.Quotient.mk (B.Fil n 1) (mapAcr f n (A.toAcr n x)) = B.uToQ n (mapU f (A.th x))) ∧
    ∀ x : Ainf l, algebraMap (Ainf l) (A.Acr 1) x = A.aTo1 (A.s (x.coeff 0)) :=
  ⟨mapAcris_acrisOfTilt f, mapAcr_expand f, mapU_sharp f, mapUnits_unitsOfTilt f, mk_mapAcr_toAcr f, algebraMap_eq_acrisOfTilt A⟩

end GlobalTheory.CompanionTheory.PAlgNat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCohomologyOfFrameStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_cohomology_of_frame : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) (E : CrystallineSemistableComparison.Pb.Frame Φ 0)
    (σ : ∀ T : C, E.D ⟶ T) (r : ℤ) (j : ℕ),
    (r < j → Subsingleton (CH.H (gr Fil r) j)) ∧
    ∀ q : ℕ, r = j + q →
      (∀ c : CH.H (gr Fil r) j, ∃ x : Idx j 0 → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) ∧
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j 0, E.form σ I.1 (x I) s) c) ∧
      ∀ x : Idx j 0 → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) →
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j 0, E.form σ I.1 (x I) s) 0 → ∀ I, x I ∈ (Fil ((q : ℤ) + 1)).S E.D := by
  intro R _ C _ Φ Fil hF E σ r j
  have hI : Limits.IsInitial E.D := Limits.IsInitial.ofUniqueHom σ fun _ f =>
    (E.bij f (fun _ => 0) (fun _ => Ideal.zero_mem _)).unique
      (fun i => i.elim0) (fun i => i.elim0)
  have hSucc (n : ℕ) : Subsingleton (CH.H (gr Fil r) (n + 1)) :=
    GlobalTheory.CompanionTheory.LocGr.H_succ_subsingleton _ hI n
  refine ⟨fun hr => ?_, fun q hq => ?_⟩
  · cases j with
    | zero =>
      exact GlobalTheory.CompanionTheory.LocGr.H_zero_subsingleton hF (by simpa using hr)
    | succ n => exact hSucc n
  · cases j with
    | succ n =>
      have : Subsingleton (CH.H (gr Fil r) (n + 1)) := hSucc n
      have : IsEmpty (Idx (n + 1) 0) := ⟨fun I => (I.1 0).elim0⟩
      refine ⟨fun c => ⟨fun I => isEmptyElim I, fun I => isEmptyElim I, ?_⟩,
        fun _ _ _ I => isEmptyElim I⟩
      unfold CrystallineSemistableComparison.Pb.Rep
      refine ⟨0, map_zero _, Subsingleton.elim _ _, fun s => ?_⟩
      have e := Fintype.sum_empty (fun I : Idx (n + 1) 0 => E.form σ I.1 (isEmptyElim I) s)
      refine Eq.trans ?_ (congrArg (Ideal.Quotient.mk _) e).symm
      exact (map_zero _).symm
    | zero =>
      have hq' : r = q := by simpa using hq
      subst hq'
      have : Unique (Idx 0 0) :=
        ⟨⟨⟨Fin.elim0, fun a => a.elim0⟩⟩, fun I => Subtype.ext (funext fun a => a.elim0)⟩
      have hform (x : Idx 0 0 → Φ.A.obj E.D) (s : ComposableArrows C 0) :
          ∑ I : Idx 0 0, E.form σ I.1 (x I) s = (Φ.A.map (σ _)).hom (x default) := by
        rw [Fintype.sum_unique]
        simp [CrystallineSemistableComparison.Pb.Frame.form]
      refine ⟨fun c => ?_, fun x _ hrep I => ?_⟩
      · obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
        obtain ⟨m, hm⟩ :=
          (CrystallineSemistableComparison.P.initial (gr Fil (q : ℤ)) E.D hI).2.2.1 f hf
        obtain ⟨m', hm'⟩ := m
        obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hm'
        refine ⟨fun _ => y, fun _ => hy, ?_⟩
        unfold CrystallineSemistableComparison.Pb.Rep
        refine ⟨f, hf, rfl, fun s => ?_⟩
        refine Eq.trans ?_ (congrArg (Ideal.Quotient.mk _) (hform (fun _ => y) s)).symm
        have h1 := congrFun (hm.trans (one_smul R f)) s
        have h2 := congrArg Subtype.val h1
        rw [show σ (s.obj (Fin.last 0)) = hI.to _ from hI.hom_ext _ _]
        exact h2.symm
      · unfold CrystallineSemistableComparison.Pb.Rep at hrep
        obtain ⟨f, hf, h0, hs⟩ := hrep
        have hf0 : f = 0 := by
          have h3 : (⟨f, hf⟩ : (CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).Z 0) ∈
              ((CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).B 0).submoduleOf
                ((CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).Z 0) :=
            (Submodule.Quotient.mk_eq_zero _).1 h0.symm
          exact (Submodule.mem_bot R).1 h3
        subst f
        have h1 := (hs (ComposableArrows.mk₀ E.D)).trans (congrArg (Ideal.Quotient.mk _) (hform x _))
        have hσ : σ ((ComposableArrows.mk₀ E.D).obj (Fin.last 0)) = 𝟙 E.D := hI.hom_ext _ _
        rw [hσ] at h1
        have h4 : (Φ.A.map (𝟙 E.D)).hom (x default) = x default := by
          rw [Φ.A.map_id]
          rfl
        have h5 : Ideal.Quotient.mk ((Fil ((q : ℤ) + 1)).S E.D) (x default) = 0 := by
          rw [← h4]
          exact h1.symm
        rw [Subsingleton.elim I default]
        exact Ideal.Quotient.eq_zero_iff_mem.1 h5
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRingAdicCompletePrimeRegular
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.TiltCompl

variable {l : ℕ} [Fact l.Prime]

theorem norm_pFlat_pos : 0 < ‖pFlat l‖ := by
  rw [preTilt_norm_def, coe_untilt_pFlat]
  exact norm_pos_iff.2 natCast_p_ne_zero_cp

theorem norm_pFlat_lt_one : ‖pFlat l‖ < 1 := by
  rw [preTilt_norm_def, coe_untilt_pFlat]
  exact IsPerfectoidField.norm_natCast_lt_one

theorem smodEq_iff (n : ℕ) (x y : Ob l) :
    x ≡ y [SMOD (Ideal.span {pFlat l} ^ n • ⊤ : Ideal (Ob l))] ↔ ‖x - y‖ ≤ ‖pFlat l‖ ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, preTilt_dvd_iff_norm_le, norm_pow]

theorem complete_tf : ∀ {l : ℕ} [Fact l.Prime],
    IsAdicComplete (Ideal.span {pFlat l}) (Ob l) ∧ pFlat l ∈ nonZeroDivisors (Ob l) := by
  intro l _
  have h0 : 0 < ‖pFlat l‖ := norm_pFlat_pos
  have h1 : ‖pFlat l‖ < 1 := norm_pFlat_lt_one
  have hlim : Filter.Tendsto (fun n : ℕ => ‖pFlat l‖ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1
  refine ⟨{ haus' := fun x hx => ?_, prec' := fun f hf => ?_ }, ?_⟩
  · have hb : ∀ n : ℕ, ‖x‖ ≤ ‖pFlat l‖ ^ n := fun n => by
      simpa using (smodEq_iff n x 0).1 (hx n)
    have : ‖x‖ ≤ 0 := ge_of_tendsto' hlim hb
    exact norm_le_zero_iff.1 this
  · have hb : ∀ {m n : ℕ}, m ≤ n → ‖f m - f n‖ ≤ ‖pFlat l‖ ^ m := fun h =>
      (smodEq_iff _ _ _).1 (hf h)
    have hc : CauchySeq f := by
      refine cauchySeq_of_le_geometric ‖pFlat l‖ 1 h1 fun n => ?_
      rw [dist_eq_norm, one_mul]
      exact hb n.le_succ
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨L, fun n => (smodEq_iff _ _ _).2 ?_⟩
    have ht : Filter.Tendsto (fun m => ‖f n - f m‖) Filter.atTop (nhds ‖f n - L‖) :=
      (tendsto_const_nhds.sub hL).norm
    refine le_of_tendsto ht ?_
    filter_upwards [Filter.eventually_ge_atTop n] with m hm using hb hm
  · exact mem_nonZeroDivisors_iff_left.2 fun x hx => by
      have := congrArg norm hx
      rw [norm_mul, norm_zero] at this
      exact norm_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h0.ne')

end GlobalTheory.CompanionTheory.TiltCompl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationLTorsionFree
section
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Lat

theorem quot_pdP_no_torsion : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ), Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), ∀ (r : ℕ) (x : Lat.A f ξ l M), (l : Lat.A f ξ l M) * x ∈ pdP (Lat.γ f ξ l M hc) r → x ∈ pdP (Lat.γ f ξ l M hc) r := by
  intro W B _ _ _ f ξ l M m hH hc r x hx
  rw [_root_.GlobalTheory.CompanionTheory.LatPdpEq.dividedPowerFiltration_eq f ξ l M m hH hc r] at hx ⊢
  rw [Ideal.mem_comap, map_mul, map_natCast] at hx
  rw [Ideal.mem_comap]
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hH.l0 Nat.cast_zero
  have hl : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hl0
  have hu : algebraMap ℚ B (l : ℚ)⁻¹ * (l : B) = 1 := by
    rw [← map_natCast (algebraMap ℚ B) l, ← map_mul, inv_mul_cancel₀ hl, map_one]
  have h2 := Ideal.mul_mem_left _ (algebraMap ℚ B (l : ℚ)⁻¹) hx
  rwa [← mul_assoc, hu, one_mul] at h2

end GlobalTheory.CompanionTheory.Lat
end

