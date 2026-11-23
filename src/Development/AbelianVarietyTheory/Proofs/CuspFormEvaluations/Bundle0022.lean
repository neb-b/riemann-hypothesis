module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PolyDerivProdColumnFunctions
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

open scoped ContDiff

theorem filter_col_toMultiset {T : Type} [Fintype T] {r : T → ℕ} {n : ℕ}
    (m : Formalism.L2.Pj.Letter T r n →₀ ℕ) (b : Fin n) :
    (Finsupp.toMultiset m).filter (fun ℓ => ℓ.2.2 = b) =
      (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm
        fun ℓ : (Σ τ : T, Fin (r τ)) => m ⟨ℓ.1, ℓ.2, b⟩)).map
        (fun ℓ : (Σ τ : T, Fin (r τ)) => (⟨ℓ.1, ℓ.2, b⟩ : Formalism.L2.Pj.Letter T r n)) := by
  classical
  have hinj : Function.Injective
      (fun ℓ : (Σ τ : T, Fin (r τ)) => (⟨ℓ.1, ℓ.2, b⟩ : Formalism.L2.Pj.Letter T r n)) := by
    intro x y h
    exact congrArg (fun ℓ : Formalism.L2.Pj.Letter T r n => (⟨ℓ.1, ℓ.2.1⟩ : Σ τ : T, Fin (r τ))) h
  ext ⟨τ, i, c⟩
  rw [Multiset.count_filter]
  by_cases h : c = b
  · subst h
    rw [if_pos rfl]
    have := Multiset.count_map_eq_count' _ (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm
        fun ℓ : (Σ τ : T, Fin (r τ)) => m ⟨ℓ.1, ℓ.2, c⟩)) hinj ⟨τ, i⟩
    rw [this]
    simp [Finsupp.count_toMultiset]
  · rw [if_neg h]
    symm
    rw [Multiset.count_eq_zero, Multiset.mem_map]
    rintro ⟨x, -, hx⟩
    exact h (congrArg (fun ℓ : Formalism.L2.Pj.Letter T r n => ℓ.2.2) hx).symm

theorem polyDeriv_prod_cols : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (T : Type) [Fintype T] (r : T → ℕ) (n : ℕ) (u : (Σ τ : T, Fin (r τ)) → V) (θ : Fin n → V → ℂ), (∀ b, Differentiable ℂ (θ b)) → ∀ P : MvPolynomial (Formalism.L2.Pj.Letter T r n) ℂ, I2.polyDeriv P (fun ℓ => (Pi.single ℓ.2.2 (u ⟨ℓ.1, ℓ.2.1⟩) : Fin n → V)) (fun z => ∏ b, θ b (z b)) 0 = ∑ m ∈ P.support, P.coeff m * ∏ b, I2.polyDeriv (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun ℓ : (Σ τ : T, Fin (r τ)) => m ⟨ℓ.1, ℓ.2, b⟩) (1 : ℂ)) u (θ b) 0 := by
  intro V _ _ _ T _ r n u θ hθ P
  classical
  have hω : ∀ b x, ContDiffAt ℂ ω (θ b) x := fun b x =>
    GlobalTheory.SCV.contDiffAt_of_differentiableOn (hθ b).differentiableOn Filter.univ_mem ω
  have hs : ∀ b, ContDiff ℂ (⊤ : ℕ∞) (θ b) := fun b =>
    contDiff_iff_contDiffAt.2 fun x => (hω b x).of_le le_top
  rw [I2.polyDeriv_eq_of_subset P _ _ _ (Finset.Subset.refl _)]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  rw [I2.pdTerm_eq_itD]
  have e : (Finsupp.toMultiset m).toList.map
      (fun ℓ : Formalism.L2.Pj.Letter T r n => (Pi.single ℓ.2.2 (u ⟨ℓ.1, ℓ.2.1⟩) : Fin n → V)) =
      ((Finsupp.toMultiset m).toList.map
        (fun ℓ : Formalism.L2.Pj.Letter T r n => ((ℓ.2.2, u ⟨ℓ.1, ℓ.2.1⟩) : Fin n × V))).map
        (fun p => Pi.single p.1 p.2) := by
    rw [List.map_map]; rfl
  rw [e, I2.itD_prod hs]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [I2.polyDeriv_monomial_one, I2.pdTerm_eq_itD]
  refine lD_perm (hω b 0) ?_
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe u, Multiset.coe_toList]
  have h := congrArg (Multiset.map fun ℓ : Formalism.L2.Pj.Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩)
    (filter_col_toMultiset m b)
  rw [Multiset.map_map] at h
  refine Eq.trans ?_ h
  conv_rhs => rw [← Multiset.coe_toList (Finsupp.toMultiset m)]
  rw [Multiset.filter_coe, Multiset.map_coe]
  unfold I2.colL
  rw [List.filter_map, List.map_map]
  rfl

end GlobalTheory.AnVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ReadingTwistedPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem AnFr.rd_twistPull : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (ψ : Over.mk x0 ⊗ A ⟶ Over.mk x0 ⊗ A) (m : Over.mk x0 ⊗ A ⟶ A) (hm : ψ ≫ snd (Over.mk x0) A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd (Over.mk x0) A).left, m.left] ![a, -b])) (s : LB.Sec (LPow A L.L b (Over.mk x0))) (s' : LB.Sec (LPow A L.L a (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ) (p : (Fin g → ℂ) → Fin g → ℂ) (v : (Fin g → ℂ) → ℂ), ψ ≫ fst (Over.mk x0) A = fst (Over.mk x0) A → IsTwistPull A L.L ψ m hm a b α s s' → Φ.Rd b s θ → (∀ z, (ptSecT A (Φ.e z)).left ≫ m.left = (Φ.e (p z)).left ∧ ∃ j : Fin 2 → L.L.ι, ⊤ ≤ (ptSecT A (Φ.e z)).left ⁻¹ᵁ LB.wchart L.L ![(snd (Over.mk x0) A).left, m.left] j ∧ valAt' (ptSecT A (Φ.e z)).left (LB.wchart L.L ![(snd (Over.mk x0) A).left, m.left] j) (α.s j).val = v z * (Φ.fr (j 0) z ^ a * Φ.fr (j 1) (p z) ^ (-b))) → Φ.Rd a s' (fun z => v z * θ (p z)) := by
  intro S A _ _ L x0 g Φ ψ m hm a b α s s' θ p v hψ ht hs hα j' z pt h1 h2 hj'
  obtain ⟨hmz, j, hj, hv⟩ := hα z
  change (vtfQ A (Φ.e z)).left ≫ m.left = _ at hmz
  change ⊤ ≤ (vtfQ A (Φ.e z)).left ⁻¹ᵁ _ at hj
  change valAt' (vtfQ A (Φ.e z)).left _ _ = _ at hv
  have h0 : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U (j 0) := by
    rw [← vtfQ_snd A (Φ.e z)]
    intro q hq
    exact LB.wchart_le L.L ![(snd (Over.mk x0) A).left, m.left] j 0 (hj hq)
  have h1' : ⊤ ≤ (Φ.e (p z)).left ⁻¹ᵁ L.L.U (j 1) := by
    rw [← hmz]
    intro q hq
    exact LB.wchart_le L.L ![(snd (Over.mk x0) A).left, m.left] j 1 (hj hq)
  have e1 : ((vtfQ A (Φ.e z)).left ≫ ψ.left) ≫ (snd (Over.mk x0) A).left = (Φ.e (p z)).left := by
    rw [Category.assoc, ← Over.comp_left, hm, hmz]
  have e2 : ((vtfQ A (Φ.e z)).left ≫ ψ.left) ≫ (fst (Over.mk x0) A).left = 𝟙 (Sp ℂ) := by
    rw [Category.assoc, ← Over.comp_left, hψ]
    exact vtfQ_fst A (Φ.e z)
  have hr := hs (j 1) (p z) _ e1 e2 h1'
  have tw := vtf_twist A L.L ht (vtfQ A (Φ.e z)).left j hj
  have hne := Φ.fr_ne (j 1) (p z) h1'
  rw [vtf_pt_uniq A (Φ.e z) pt h1 h2]
  refine vtf_read A L.L s' (Φ.e z) (fun i => Φ.fr i z) (fun i i' h => Φ.fr_g i i' z h) (j 0) j' h0 hj' _ ?_
  refine tw.trans ?_
  refine (congrArg₂ (· * ·) hv hr).trans ?_
  have hz : Φ.fr (j 1) (p z) ^ b ≠ 0 := zpow_ne_zero _ hne
  rw [zpow_neg]
  field_simp

end GlobalTheory.AnVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SectionReadingExistsUniqueIsTheta
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem isHolFam_vtfQ {x0 : Sp ℂ ⟶ S} {g : ℕ} (e : (Fin g → ℂ) → (Over.mk x0 ⟶ A))
    (hol : IsHolFam (fun z => (e z).left)) : IsHolFam (fun z => (vtfQ A (e z)).left) := by
  have he : ∀ z, (e z).left ≫ A.hom = x0 := fun z => Over.w (e z)
  have h := isHolFam_vtfLift A.hom x0 (fun z => (e z).left) he hol
  let σ : pullback A.hom x0 ⟶ (Over.mk x0 ⊗ A).left := (pullbackSymmetry A.hom x0).hom
  have key : ∀ z, (vtfQ A (e z)).left = vtfLift A.hom x0 (fun z => (e z).left) he z ≫ σ := by
    intro z
    symm
    apply vtf_pt_uniq
    · have : σ ≫ (snd (Over.mk x0) A).left = pullback.fst A.hom x0 :=
        pullbackSymmetry_hom_comp_snd A.hom x0
      rw [Category.assoc, this]
      exact pullback.lift_fst _ _ _
    · have : σ ≫ (fst (Over.mk x0) A).left = pullback.snd A.hom x0 :=
        pullbackSymmetry_hom_comp_fst A.hom x0
      rw [Category.assoc, this]
      exact pullback.lift_snd _ _ _
  intro V φ
  have h1 := h (σ ⁻¹ᵁ V) ((σ.app V).hom φ)
  have h2 : (fun z => valAt' (vtfQ A (e z)).left V φ) = fun z =>
      valAt' (vtfLift A.hom x0 (fun z => (e z).left) he z) (σ ⁻¹ᵁ V) ((σ.app V).hom φ) := by
    funext z
    rw [key]
    exact (valAt'_comp _ σ V φ).symm
  have h3 : {z | ⊤ ≤ (vtfQ A (e z)).left ⁻¹ᵁ V} =
      {z | ⊤ ≤ vtfLift A.hom x0 (fun z => (e z).left) he z ⁻¹ᵁ (σ ⁻¹ᵁ V)} := by
    ext z
    rw [Set.mem_ofPred_eq, key]
    rfl
  exact ⟨h3 ▸ h1.1, h3 ▸ h2 ▸ h1.2⟩

variable {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem AnFr.exists_chart_e (z : Fin g → ℂ) : ∃ j, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j := by
  have h : (Φ.e z).left cpt ∈ ⨆ i, L.L.U i := by rw [L.isLB.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨j, top_le_of_mem hj⟩

theorem AnFr.rd_val {k : ℤ} {F : LB.Sec (LPow A L.L k (Over.mk x0))} {θ : (Fin g → ℂ) → ℂ} (h : Φ.Rd k F θ)
    (j : L.L.ι) (z : Fin g → ℂ) (hj : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j) :
    valAt' (vtfQ A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) =
      θ z * Φ.fr j z ^ k :=
  h j z _ (vtfQ_snd A _) (vtfQ_fst A _) hj

theorem AnFr.rd_iff (k : ℤ) (F : LB.Sec (LPow A L.L k (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ) :
    Φ.Rd k F θ ↔ ∀ z, ∃ j, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j ∧
      valAt' (vtfQ A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) =
        θ z * Φ.fr j z ^ k := by
  constructor
  · intro h z
    obtain ⟨j, hj⟩ := Φ.exists_chart_e z
    exact ⟨j, hj, Φ.rd_val h j z hj⟩
  · intro h j' z pt h1 h2 hj'
    obtain ⟨j, hj, hv⟩ := h z
    rw [vtf_pt_uniq A (Φ.e z) pt h1 h2]
    exact vtf_read A L.L F (Φ.e z) (fun j => Φ.fr j z) (fun a b hab => Φ.fr_g a b z hab) j j' hj hj' _ hv

theorem AnFr.rd_eq_div {k : ℤ} {F : LB.Sec (LPow A L.L k (Over.mk x0))} {θ : (Fin g → ℂ) → ℂ} (h : Φ.Rd k F θ)
    (j : L.L.ι) (z : Fin g → ℂ) (hj : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j) :
    θ z = valAt' (vtfQ A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) /
      Φ.fr j z ^ k := by
  rw [Φ.rd_val h j z hj, mul_div_cancel_right₀ _ (zpow_ne_zero _ (Φ.fr_ne j z hj))]

theorem AnFr.existsUnique_rd (k : ℤ) (F : LB.Sec (LPow A L.L k (Over.mk x0))) : ∃! θ, Φ.Rd k F θ := by
  choose c hc using Φ.exists_chart_e
  refine ⟨fun z => valAt' (vtfQ A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => c z))
    (F.f (fun _ => c z)) / Φ.fr (c z) z ^ k, ?_, fun θ hθ => ?_⟩
  · refine (Φ.rd_iff k F _).2 fun z => ⟨c z, hc z, ?_⟩
    rw [div_mul_cancel₀ _ (zpow_ne_zero _ (Φ.fr_ne _ z (hc z)))]
  · funext z
    exact Φ.rd_eq_div hθ (c z) z (hc z)

theorem AnFr.e_add_lat {a : Fin g → ℂ} (ha : a ∈ Φ.lat) (z : Fin g → ℂ) : Φ.e (z + a) = Φ.e z := by
  rw [Φ.e_add, (Φ.e_ker a).2 ha, _root_.mul_one]

theorem AnFr.isTh_of_rd {k : ℤ} {F : LB.Sec (LPow A L.L k (Over.mk x0))} {θ : (Fin g → ℂ) → ℂ}
    (h : Φ.Rd k F θ) : Φ.IsTh k θ := by
  constructor
  · intro z0
    obtain ⟨j, hj⟩ := Φ.exists_chart_e z0
    have hO : IsOpen {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j} := (Φ.hol (L.L.U j) 0).1
    have hv := (isHolFam_vtfQ Φ.e Φ.hol ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j))).2
    have hv' := hv.mono (s := {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j})
      (fun z hz => vtf_chart A L.L k (Φ.e z) (fun _ => j) hz)
    have hd : DifferentiableOn ℂ θ {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j} :=
      (hv'.mul ((Φ.fr_hol j).zpow (m := -k) (Or.inl fun z hz => Φ.fr_ne j z hz))).congr fun z hz => by
        rw [Φ.rd_eq_div h j z hz, div_eq_mul_inv, ← zpow_neg]
        rfl
    exact hd.differentiableAt (hO.mem_nhds hj)
  · intro a ha z
    obtain ⟨j, hj⟩ := Φ.exists_chart_e z
    have hj' : ⊤ ≤ (Φ.e (z + a)).left ⁻¹ᵁ L.L.U j := by rw [Φ.e_add_lat ha]; exact hj
    have h1 := Φ.rd_val h j z hj
    have h2 := Φ.rd_val h j (z + a) hj'
    rw [Φ.e_add_lat ha, h1, Φ.fr_per a ha j z hj, mul_zpow] at h2
    apply mul_right_cancel₀ (zpow_ne_zero k (Φ.fr_ne j (z + a) hj'))
    rw [← h2, AnFr.fac]
    ring

theorem reading_existsUnique_isTh : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (F : LB.Sec (LPow A L.L k (Over.mk x0))), (∃! θ, Φ.Rd k F θ) ∧ (∀ θ, Φ.Rd k F θ → Φ.IsTh k θ) ∧ ∀ θ, Φ.Rd k F θ ↔ ∀ z, ∃ j, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j ∧ valAt' (ptSecT A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) = θ z * Φ.fr j z ^ k := by
  intro S A _ _ L x0 g Φ k F
  exact ⟨Φ.existsUnique_rd k F, fun θ h => Φ.isTh_of_rd h, fun θ => Φ.rd_iff k F θ⟩

end GlobalTheory.AnVal
end
end

