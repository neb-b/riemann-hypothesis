module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1076
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotKltAtOfIsNkltCentre
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem not_kltAt_of_isNkltCentre (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ) (hp : IsProjOver p)
    (hn : topologicalKrullDim X = n) (Γ : X → ℚ) (z x : X) (h : IsNkltCentre p n Γ z)
    (hz : z ⤳ x) : ¬ KltAt p n Γ x := by
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  rintro ⟨η', m', g', h₁, h₂, h₃, h₄⟩
  obtain ⟨E, η, m, g, hη, hm, hg, hE, hd⟩ := h
  have h₅ : IsLogEqn p Γ η' z m' g' := fun w hw => h₃ w (hw.trans hz)
  have h₆ := h₄ E (hE.1.of_specializes hz)
  rw [discrep_eq hn h₁ hη h₂ hm h₅ hg hE.1] at h₆
  exact h₆.not_ge hd

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OppositeIsotropicFlagStabilizerNotRaiseWeight
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact

namespace GlobalTheory.UAut.OppFlagWeight

theorem weight_of_triangular {A : Type} [CommRing A] {n r : ℕ} {X Y : Matrix (Fin n) (Fin r) A}
    {L T : Matrix (Fin r) (Fin n) A} {x : Matrix (Fin n) (Fin n) A} {B B' : Matrix (Fin r) (Fin r) A}
    {d : Fin r → ℕ} {M : ℕ} (hd : ∀ j, d j < M)
    (hLX : L * X = 1) (hTY : T * Y = 1) (hLY : L * Y = 0)
    (hB : x * Y = Y * B) (hB' : L * x = B' * L) (tB : ∀ i j, d j < d i → B i j = 0) (tB' : ∀ i j, d i < d j → B' i j = 0)
    (ε : Option (Fin r ⊕ Fin r) → Matrix (Fin n) (Fin n) A)
    (e0 : ε none = 1 - (X * L + Y * T)) (e1 : ∀ j, ε (some (.inl j)) = X * single j j (1 : A) * L)
    (e2 : ∀ j, ε (some (.inr j)) = Y * single j j (1 : A) * T) :
    ∀ a b, wt d M b < wt d M a → ε a * x * ε b = 0 := by
  have k0 : ε none * Y = 0 := by
    rw [e0, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hLY, hTY]; simp
  have k1 : L * ε none = 0 := by
    rw [e0, Matrix.mul_sub, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hLY, hLX]; simp
  have k2 : ∀ (m : Matrix (Fin n) (Fin n) A) j, m * Y = 0 → m * x * ε (some (.inr j)) = 0 := fun m j h => by
    rw [e2, Matrix.mul_assoc Y, ← Matrix.mul_assoc, Matrix.mul_assoc m, hB, ← Matrix.mul_assoc m, h]; simp
  rintro (_ | i | i) (_ | j | j) hab
  · simp [wt] at hab
  · have := hd j; simp [wt] at hab; omega
  · exact k2 _ j k0
  · rw [e1, Matrix.mul_assoc _ L, hB', ← Matrix.mul_assoc, Matrix.mul_assoc _ L, k1, Matrix.mul_zero]
  · rw [e1, e1, sandwich_eq_zero hLX, hB', Matrix.mul_assoc, hLX, Matrix.mul_one]
    exact tB' i j (by simp [wt] at hab; omega)
  · exact k2 _ j (by rw [e1, Matrix.mul_assoc, hLY, Matrix.mul_zero])
  · have := hd i; simp [wt] at hab; omega
  · have := hd i; have := hd j; simp [wt] at hab; omega
  · rw [e2, e2, sandwich_eq_zero hTY, Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hTY, Matrix.one_mul]
    exact tB i j (by simp [wt] at hab; omega)

theorem not_raise_of_mem_parFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) (M : ℕ), (∀ j, d j < M) → Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ p ∈ parFlag σ J Y d, ∀ a b, wt d M b < wt d M a → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J p).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0 := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y d M hd _ hY hXY p hp
  obtain ⟨⟨B, hB, eB⟩, B', hB', eB'⟩ := hp
  have cc : ∀ {m p : Type} (A : Matrix m p E), Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) A) = A := fun A =>
    Matrix.ext fun i j => sigma_sigma h _
  have hYX : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (Formalism.UG.cT (σ : E →+* E)) hXY
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  have f := form_mul_of_mul_cols eB'
  rw [inv_inv] at f
  set φ := inclR (F := F) (E := E) (AF F) with hφ
  have adj : ∀ Z : Matrix (Fin r) (Fin r) E, adjA σ J ((X * Z * (Formalism.UG.cT (σ : E →+* E) Y * J)).map φ) =
      Y.map φ * (Formalism.UG.cT (σ : E →+* E) Z).map φ * (Formalism.UG.cT (σ : E →+* E) X * J).map φ := fun Z => by
    rw [adjA_map, ← Matrix.map_mul, ← Matrix.map_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc J⁻¹, Matrix.nonsing_inv_mul _ (det_isUnit hJ), Matrix.one_mul]
  refine weight_of_triangular (X := X.map φ) (Y := Y.map φ) (L := (Formalism.UG.cT (σ : E →+* E) Y * J).map φ)
    (T := (Formalism.UG.cT (σ : E →+* E) X * J).map φ) hd ?_ ?_ ?_ eB f (fun i j hij => hB hij) (fun i j hij => ?_) _ ?_
    (fun j => idemA_eq _ _ j) (fun j => ?_)
  · rw [← Matrix.map_mul, hYX, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, hY, Matrix.map_zero _ (map_zero _)]
  · show sigR (AF F) σ (B' j i) = 0
    rw [hB' hij, map_zero]
  · have := adj 1
    rw [Matrix.mul_one, Formalism.UG.cT_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this
    simp only [fam, Option.elim, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, sum_idemA, this, Matrix.map_mul]
  · refine (adj (single j j 1)).trans ?_
    congr 2
    ext a b
    by_cases h1 : j = a <;> by_cases h2 : j = b <;> simp [Formalism.UG.cT, single, h1, h2]

end GlobalTheory.UAut.OppFlagWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralRestrictedProductEqProd
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RestrProd

theorem twOrb_restrProd : ∀ (ι G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, T2Space (H i)] (p : ∀ i, G →* H i) (K : Subgroup G) (KH : ∀ i, Subgroup (H i)) (δ : G) (f : ∀ i, H i → ℂ), (∀ i, Continuous (p i)) → (∀ x y : G, (∀ i, p i x = p i y) → x = y) → (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ C : ∀ i, Set (H i), (∀ i, IsCompact (C i)) → (∀ᶠ i in cofinite, C i = KH i) → IsCompact {x : G | ∀ i, p i x ∈ C i}) → (∀ i, IsCompact (KH i : Set (H i))) → (∀ i, ∀ a ∈ twCent (MonoidHom.id (H i)) (p i δ), ∀ b ∈ twCent (MonoidHom.id (H i)) (p i δ), a * b = b * a) → (∀ i (x : H i), twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ∧ (twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) ≠ 0) → (∀ i (x : H i), (rStab fun k : KH i => f i ((x * k)⁻¹ * p i δ * (x * k))).index ≠ 0) → (∀ i, {q : DoubleCoset.Quotient (twCent (MonoidHom.id (H i)) (p i δ) : Set (H i)) (KH i : Set (H i)) | ∃ k ∈ KH i, f i ((Quotient.out q * k)⁻¹ * p i δ * (Quotient.out q * k)) ≠ 0}.Finite) → (∀ᶠ i in cofinite, p i δ ∈ KH i ∧ f i = (KH i : Set (H i)).indicator 1 ∧ (∀ g : H i, g⁻¹ * p i δ * g ∈ KH i → ∃ t ∈ twCent (MonoidHom.id (H i)) (p i δ), t⁻¹ * g ∈ KH i) ∧ cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ≤ KH i) → twOrb (MonoidHom.id G) K δ (fun x => ∏ᶠ i, f i (p i x)) = ∏ᶠ i, twOrb (MonoidHom.id (H i)) (KH i) (p i δ) (f i) := by
  intro ι G _ _ _ H _ _ _ _ p K KH δ f hpc hinj hglue hfin hK hcpt hKc hcomm hloc hstab hsupp hgood
  have hT : ∀ x, x ∈ twCent (MonoidHom.id G) δ ↔ ∀ i, p i x ∈ twCent (MonoidHom.id (H i)) (p i δ) := by
    intro x
    simp only [GlobalTheory.TwOrbConj.mem_twCent, MonoidHom.id_apply]
    constructor
    · intro h i
      rw [← map_mul, h, map_mul]
    · intro h
      apply hinj
      intro i
      rw [map_mul, h i, map_mul]
  have hC := _root_.GlobalTheory.BCT.mem_cptPart_iff_local ι G H p KH _ _ hpc hfin hcpt hKc hT hcomm
  have hCT : ∀ i, cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ≤ twCent (MonoidHom.id (H i)) (p i δ) :=
    fun i => (Subgroup.closure_le _).2 (fun t ht => ht.1)
  have havg1 : ∀ (M : Type) [Group M], avg (fun _ : M => (1 : ℂ)) = 1 := by
    intro M _
    have hR : rStab (fun _ : M => (1 : ℂ)) = ⊤ := by
      ext k
      simp [GlobalTheory.TwOrbConj.mem_rStab]
    unfold avg
    rw [hR, Subgroup.index_top]
    haveI : Subsingleton (M ⧸ (⊤ : Subgroup M)) := QuotientGroup.subsingleton_quotient_top
    haveI : Unique (M ⧸ (⊤ : Subgroup M)) := uniqueOfSubsingleton (QuotientGroup.mk 1)
    simp [finsum_unique]
  have hs : ∀ g, GlobalTheory.TwOrbConj.summand (MonoidHom.id G) K δ (fun x => ∏ᶠ i, f i (p i x)) g =
      ∏ᶠ i, GlobalTheory.TwOrbConj.summand (MonoidHom.id (H i)) (KH i) (p i δ) (f i) (p i g) := by
    intro g
    have hrel := GlobalTheory.T.relIndex_inf_conj_eq_finprod_restrictedProduct ι G H p K _ _ KH _ _ g hglue hfin hK hT hC hCT (fun i => hloc i (p i g))
      (hgood.mono fun i h => h.2.2.2)
    have hu1 : ∀ᶠ i in cofinite, ∀ k : KH i, f i ((p i g * k)⁻¹ * p i δ * (p i g * k)) = 1 := by
      filter_upwards [hgood, hfin g] with i h hg k
      rw [h.2.1]
      apply Set.indicator_of_mem
      exact (KH i).mul_mem ((KH i).mul_mem ((KH i).inv_mem ((KH i).mul_mem hg k.2)) h.1) ((KH i).mul_mem hg k.2)
    have havg := _root_.GlobalTheory.AvgRestr.avg_restrProd ι G H p K KH hK (fun i k => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) hglue
      (fun i => hstab i (p i g)) hu1
    have hr1 : ∀ᶠ i in cofinite, (((twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) : ℕ) : ℂ) = 1 := by
      filter_upwards [hgood, hfin g] with i h hg
      rw [GlobalTheory.TwOrbConj.map_conj_self _ hg, Subgroup.relIndex_eq_one.2 (le_inf (hCT i) h.2.2.2), Nat.cast_one]
    have ha1 : ∀ᶠ i in cofinite, avg (fun k : KH i => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) = 1 := by
      filter_upwards [hu1] with i h
      rw [show (fun k : KH i => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) = fun _ => 1 from funext h]
      exact havg1 _
    have e1 : avg (fun k : K => ∏ᶠ i, f i (p i ((g * ↑k)⁻¹ * δ * (MonoidHom.id G) (g * ↑k)))) =
        ∏ᶠ i, avg (fun k : KH i => f i ((p i g * k)⁻¹ * p i δ * (p i g * k))) := by
      rw [← havg]
      congr 1
      funext k
      simp [map_mul, map_inv]
    unfold GlobalTheory.TwOrbConj.summand
    simp only [MonoidHom.id_apply] at e1 ⊢
    have hN : Function.HasFiniteMulSupport fun i => (twCent (MonoidHom.id (H i)) (p i δ) ⊓
        (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) := by
      have : ∀ᶠ i in cofinite, (twCent (MonoidHom.id (H i)) (p i δ) ⊓
          (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) = 1 := by
        filter_upwards [hgood, hfin g] with i h hg
        rw [GlobalTheory.TwOrbConj.map_conj_self _ hg, Subgroup.relIndex_eq_one.2 (le_inf (hCT i) h.2.2.2)]
      exact Filter.eventually_cofinite.1 this
    have hcast := map_finprod (Nat.castRingHom ℂ) hN
    simp only [eq_natCast] at hcast
    rw [e1, hrel, hcast, ← finprod_mul_distrib (Filter.eventually_cofinite.1 hr1) (Filter.eventually_cofinite.1 ha1)]
  rw [GlobalTheory.TwOrbConj.twOrb_eq]
  simp only [GlobalTheory.TwOrbConj.twOrb_eq]
  refine _root_.GlobalTheory.DoubleCosetEuler.finsum_doubleCoset_eq_finprod_local ι G H p _ K _ KH _ _ hglue hfin hK hT ?_ ?_ ?_ hs
  · intro i t ht k hk x
    exact GlobalTheory.TwOrbConj.summand_rep _ _ _ _ x ht hk
  · intro i
    refine (hsupp i).subset ?_
    intro q hq
    by_contra hcon
    apply hq
    have h0 : (fun k : KH i => f i ((Quotient.out q * k)⁻¹ * p i δ * (MonoidHom.id (H i)) (Quotient.out q * k))) =
        fun _ => 0 := by
      funext k
      by_contra hk
      exact hcon ⟨k, k.2, hk⟩
    unfold GlobalTheory.TwOrbConj.summand
    rw [h0]
    simp [avg]
  · filter_upwards [hgood] with i h x
    rw [h.2.1]
    exact _root_.GlobalTheory.TwOrbGood.summand_goodplace (H i) (KH i) (p i δ) h.1 h.2.2.2 h.2.2.1 x

end GlobalTheory.RestrProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralUnitIndicatorEventuallyOneClass
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.OrbUnit
open DoubleCoset

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have h1 : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [rStab]
  unfold avg
  rw [h1, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := ⟨⟨QuotientGroup.mk 1⟩, fun a => Subsingleton.elim _ _⟩
  rw [finsum_unique]
  simp

theorem twOrb_unit {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (γ : G)
    (horb : ∀ g₁ g₂ : G, g₁⁻¹ * γ * g₁ ∈ K → g₂⁻¹ * γ * g₂ ∈ K →
      ∃ t ∈ twCent (MonoidHom.id G) γ, ∃ k ∈ K, g₂ = t * g₁ * k)
    (hcpt : ∀ g : G, g⁻¹ * γ * g ∈ K →
      cptPart (twCent (MonoidHom.id G) γ) ≤ K.map (MulAut.conj g).toMonoidHom) :
    twOrb (MonoidHom.id G) K γ ((K : Set G).indicator 1) = if ∃ g : G, g⁻¹ * γ * g ∈ K then 1 else 0 := by
  classical
  set T := twCent (MonoidHom.id G) γ with hT
  have hTle : cptPart T ≤ T := by
    unfold cptPart
    rw [Subgroup.closure_le]
    intro t ht; exact ht.1
  have hterm : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G),
      ((((T ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart T) : ℕ) : ℂ) *
        avg fun k : K => (K : Set G).indicator 1 ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k)))
      = if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then 1 else 0 := by
    intro q
    have hconst : (fun k : K => (K : Set G).indicator (1 : G → ℂ)
        ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k)))
        = fun _ => if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then 1 else 0 := by
      funext k
      have he : (Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k)
          = (k : G)⁻¹ * ((Quotient.out q)⁻¹ * γ * Quotient.out q) * k := by
        simp only [MonoidHom.id_apply]; group
      rw [he]
      by_cases hm : (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K
      · have : (k : G)⁻¹ * ((Quotient.out q)⁻¹ * γ * Quotient.out q) * k ∈ K :=
          K.mul_mem (K.mul_mem (K.inv_mem k.2) hm) k.2
        simp [Set.indicator_of_mem this, hm]
      · have : (k : G)⁻¹ * ((Quotient.out q)⁻¹ * γ * Quotient.out q) * k ∉ K := by
          intro h; apply hm
          have := K.mul_mem (K.mul_mem k.2 h) (K.inv_mem k.2)
          simpa [mul_assoc] using this
        simp [Set.indicator_of_notMem this, hm]
    rw [hconst, avg_const]
    split_ifs with hm
    · rw [(Subgroup.relIndex_eq_one).2 (le_inf hTle (hcpt _ hm))]; simp
    · simp
  rw [twOrb, finsum_congr hterm]
  split_ifs with hex
  · obtain ⟨g₀, hg₀⟩ := hex
    have hgood : ∀ g : G, g ∈ doubleCoset g₀ (T : Set G) (K : Set G) → g⁻¹ * γ * g ∈ K := by
      intro g hg
      obtain ⟨t, ht, k, hk, rfl⟩ := mem_doubleCoset.1 hg
      have htc : t * γ = γ * t := by simpa [hT, twCent] using ht
      have : (t * g₀ * k)⁻¹ * γ * (t * g₀ * k) = k⁻¹ * (g₀⁻¹ * γ * g₀) * k := by
        have : t⁻¹ * γ * t = γ := by rw [mul_assoc, ← htc, ← mul_assoc, inv_mul_cancel, one_mul]
        calc (t * g₀ * k)⁻¹ * γ * (t * g₀ * k) = k⁻¹ * (g₀⁻¹ * (t⁻¹ * γ * t) * g₀) * k := by group
          _ = _ := by rw [this]
      rw [this]; exact K.mul_mem (K.mul_mem (K.inv_mem hk) hg₀) hk
    rw [finsum_eq_single _ (DoubleCoset.mk T K g₀)]
    · rw [if_pos]
      obtain ⟨h, hh, k, hk, he⟩ := DoubleCoset.mk_out_eq_mul T K g₀
      apply hgood
      rw [he]; exact mem_doubleCoset.2 ⟨h, hh, k, hk, rfl⟩
    · intro q hq
      rw [if_neg]
      intro hm
      apply hq
      obtain ⟨t, ht, k, hk, he⟩ := horb g₀ (Quotient.out q) hg₀ hm
      rw [← DoubleCoset.out_eq' q, DoubleCoset.eq]
      exact ⟨t⁻¹, T.inv_mem ht, k⁻¹, K.inv_mem hk, by rw [he]; group⟩
  · push_neg at hex
    rw [finsum_eq_zero_of_forall_eq_zero]
    intro q; rw [if_neg (hex _)]

end GlobalTheory.BCT.OrbUnit

namespace GlobalTheory.BCT.OrbUnit

theorem orbUnit_ae : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ∀ γ : UL n w, γ.1.val.charpoly = atPl w P → (twOrb (MonoidHom.id _) (KL n w) γ ((KL n w : Set (UL n w)).indicator 1) = if ∃ g : UL n w, g⁻¹ * γ * g ∈ KL n w then 1 else 0) ∧ kapSign n w (atPl w P) γ.1 = 1 ∧ ∀ Q₁ : (w.adicCompletion E)[X], Q₁ ∣ atPl w P → (∃ g : UL n w, g⁻¹ * γ * g ∈ KL n w) → kapSign n w Q₁ γ.1 = 1 := by
  intro E _ _ _ _ n _ S _ P hP
  filter_upwards [_root_.GlobalTheory.IntCop.eventually_integral_coprime E P hP.2.2.1] with w hw
  obtain ⟨P₀, hmap, hcop⟩ := hw
  obtain ⟨hσσ, hv⟩ := _root_.GlobalTheory.BCT.cj_involutive_valuation E w
  intro γ hγ
  have hγ' : γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
    rw [hγ, hmap]
  refine ⟨?_, ?_, ?_⟩
  · exact twOrb_unit (KL n w) γ (_root_.GlobalTheory.BCT.OrbitT.orbit_main E n w hσσ hv P₀ hcop γ hγ') (_root_.GlobalTheory.CptCent.cptPart_le_conj_KL E n w P₀ hcop γ hγ')
  · rw [← hγ]; exact _root_.GlobalTheory.BCT.KapSignFull.kapSign_charpoly_eq_one E n w hv γ.1
  · rintro Q₁ hQ ⟨g, hg⟩
    rw [← _root_.GlobalTheory.BCT.kapSign_conj E n w hv Q₁ γ g]
    refine _root_.GlobalTheory.BCT.kapSign_eq_one_of_integral E n w hσσ hv P₀ hcop (g⁻¹ * γ * g) ?_ hg Q₁ (by rw [hmap]; exact hQ)
    rw [← hγ']
    have : ((g⁻¹ * γ * g : UL n w) : GLw n w).val =
        ((g : GLw n w)⁻¹ : GLw n w).val * (γ : GLw n w).val * (g : GLw n w).val := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    rw [this, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

end GlobalTheory.BCT.OrbUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCoordinatesFrameRationalIsometry
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.GeoLevel

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
private lemma mat_lact_castFr_eq_map_mul {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)}
    (hΨ : Ψ = Ψ') (a : GL (Fin r) E) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (τ : E →+* ℂ) (hτ : τ ∈ Ψ')
    (hτ₀ : τ ∈ Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact a (_root_.GlobalTheory.Dict.castFr hΨ x)) ⟨τ, hτ⟩ =
      (a : Matrix (Fin r) (Fin r) E).map τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ₀⟩ := by
  rfl

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
private lemma emb_mulVec_eq_map_mulVec_emb {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (τ : E →+* ℂ) (A : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (A *ᵥ v) = (A.map τ) *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v := by
  funext k
  set_option synthInstance.maxHeartbeats 100000 in
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
private lemma col_mul_eq_mulVec_col' {r : ℕ} (A M : Matrix (Fin r) (Fin r) ℂ) (j : Fin r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.col (A * M) j = A *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.col M j := by
  funext k
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mulVec, dotProduct, Matrix.mul_apply]


open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
theorem _root_.GlobalTheory.GeoLevel.perFr_lact_of_isMatch : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (r : ℕ) (X X' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (a : GL (Fin r) E)
    (h : _root_.GlobalTheory.LevelCusp.IsMatch X X' a) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (v : Fin r → E)
    (τ : E →+* ℂ) (i : ℕ),
    _root_.Formalism.L2.PjFree.perFr X' (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact a (_root_.GlobalTheory.Dict.castFr h.psi x))
        ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = _root_.Formalism.L2.PjFree.perFr X x v τ i := by
  intro E _ _ _ r X X' a h x v τ i
  have hΨ := h.psi
  have hp := h.p0
  have hA : IsUnit ((a : Matrix (Fin r) (Fin r) E).map τ).det := by
    have h₀ := (Matrix.isUnits_det_units a).map τ
    rwa [RingHom.map_det] at h₀
  unfold _root_.Formalism.L2.PjFree.perFr
  by_cases hτ : τ ∈ X.Ψ
  · have hτ' : τ ∈ X'.Ψ := hΨ ▸ hτ
    rw [dite_eq_left hτ', dite_eq_left hτ]
    by_cases hi : X.p0 + i < r
    · have hi' : X'.p0 + i < r := hp ▸ hi
      rw [dite_eq_left hi', dite_eq_left hi]
      have hfin : (⟨X'.p0 + i, hi'⟩ : Fin r) = ⟨X.p0 + i, hi⟩ := Fin.ext (by simp [hp])
      rw [hfin, mat_lact_castFr_eq_map_mul hΨ a x τ hτ' hτ, emb_mulVec_eq_map_mulVec_emb, Matrix.mul_inv_rev,
        Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]
    · have hi' : ¬ X'.p0 + i < r := hp ▸ hi
      rw [dite_eq_right hi', dite_eq_right hi]
  · have hτ' : τ ∉ X'.Ψ := hΨ ▸ hτ
    rw [dite_eq_right hτ', dite_eq_right hτ]
    by_cases hσ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ ∈ X.Ψ
    · have hσ' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ ∈ X'.Ψ := hΨ ▸ hσ
      rw [dite_eq_left hσ', dite_eq_left hσ]
      by_cases hj : X.p0 - 1 - i < r
      · have hj' : X'.p0 - 1 - i < r := hp ▸ hj
        rw [dite_eq_left hj', dite_eq_left hj]
        have hfin : (⟨X'.p0 - 1 - i, hj'⟩ : Fin r) = ⟨X.p0 - 1 - i, hj⟩ := Fin.ext (by simp [hp])
        rw [hfin, mat_lact_castFr_eq_map_mul hΨ a x _ hσ' hσ, col_mul_eq_mulVec_col', emb_mulVec_eq_map_mulVec_emb]
        exact h.hermC_eq _ _ _
      · have hj' : ¬ X'.p0 - 1 - i < r := hp ▸ hj
        rw [dite_eq_right hj', dite_eq_right hj]
    · have hσ' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ ∉ X'.Ψ := hΨ ▸ hσ
      rw [dite_eq_right hσ', dite_eq_right hσ]

end GlobalTheory.GeoLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiolaIdentityWirtingerAntiholomorphicStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piola_identity_wirtingerAntiholomorphic : ∀ {n : ℕ} (f : Fin n → V n → ℂ) (j : Fin n) (v : V n), (∀ i, i ≠ j → ContDiffAt ℝ 2 (f i) v) → ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) * dbar (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) = 0 := by
  first | exact @GlobalTheory.GoodTop.piola_dbar | exact GlobalTheory.GoodTop.piola_dbar | (intros; apply GlobalTheory.GoodTop.piola_dbar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffConjStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedTopChernCoeff_conj : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (P : Matrix r r ℂ), IsUnit P.det → mixTop (fun i a b => P⁻¹ * K i a b * P) = mixTop K := by
  first | exact @GlobalTheory.GoodTop.mixTop_conj | exact GlobalTheory.GoodTop.mixTop_conj | (intros; apply GlobalTheory.GoodTop.mixTop_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffSlotLinear
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem position_eq_update {n : ℕ} {α : Type} [Zero α] (K₁ L K₀ : α) (j : Fin n) :
    intersection_update_fsHerm_neg_one K₁ L K₀ j = Function.update (intersection_update_fsHerm_neg_one K₁ 0 K₀ j) j L := by
  funext i
  by_cases h : i = j
  · subst h; simp [intersection_update_fsHerm_neg_one]
  · simp [intersection_update_fsHerm_neg_one, Function.update_of_ne h, h]

theorem mixTop_position_linear {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K₁ K₀ L L' : EndValuedForm11Coeffs n r)
    (s t : ℂ) (j : Fin n) :
    mixTop (intersection_update_fsHerm_neg_one K₁ (s • L + t • L') K₀ j) = s * mixTop (intersection_update_fsHerm_neg_one K₁ L K₀ j) + t * mixTop (intersection_update_fsHerm_neg_one K₁ L' K₀ j) := by
  rw [position_eq_update, position_eq_update K₁ L, position_eq_update K₁ L', _root_.GlobalTheory.GoodTop.mixTop_update_add, _root_.GlobalTheory.GoodTop.mixTop_update_smul, _root_.GlobalTheory.GoodTop.mixTop_update_smul]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeEqIffSameIntegralGLCosetStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackLattice_eq_iff_same_integralGL_coset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) → ∀ g g' : GLw n w, pullLat w B ψ g = pullLat w B ψ g' → g⁻¹ * g' ∈ GlobalTheory.LFun.KGL w (n := n) := by
  first | exact @GlobalTheory.KapOrb.PullInj.main | exact GlobalTheory.KapOrb.PullInj.main | (intros; apply GlobalTheory.KapOrb.PullInj.main <;> assumption)
end

