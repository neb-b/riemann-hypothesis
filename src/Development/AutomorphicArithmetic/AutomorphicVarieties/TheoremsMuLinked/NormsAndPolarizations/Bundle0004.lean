module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.RiEntries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.DualRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.ModelSmall
section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem model_small {l : ℕ} [Fact l.Prime] {ι : Type} [Finite ι] (x : ι → Qbar l) :
    ∃ b : Qbar l, b ≠ 0 ∧ ‖b‖ ≤ 1 ∧ ∀ i, ‖b * x i‖ ≤ 1 := by
  obtain ⟨M, hM⟩ := (Set.finite_range fun i => ‖x i‖).bddAbove
  have h1 : (0 : ℝ) < max M 1 := lt_max_of_lt_right one_pos
  obtain ⟨b, hb0, hb⟩ := NormedField.exists_norm_lt (Qbar l) (inv_pos.2 h1)
  refine ⟨b, norm_pos_iff.1 hb0, hb.le.trans (inv_le_one_of_one_le₀ (le_max_right _ _)), fun i => ?_⟩
  rw [norm_mul, ← inv_mul_cancel₀ h1.ne']
  exact mul_le_mul hb.le ((hM ⟨i, rfl⟩).trans (le_max_left _ _)) (norm_nonneg _) (inv_pos.2 h1).le

private theorem model_ordAt {l : ℕ} [Fact l.Prime] {n : ℕ} {F : GFrame l} {K : Type} [CommRing K]
    {ρ : F.G₀ →* GL (Fin n) K} {v : F.Vl} {ψ : Fin n → F.Gv v →* Kˣ} {z : F.G₀ → Matrix (Fin n) (Fin n) K}
    {w : GL (Fin n) K} {Y : Matrix (Fin n) (Fin n) K} (h : OrdAt F ρ v ψ z w Y) (a : K) :
    OrdAt F ρ v ψ (fun g => a • z g) w (a • Y) := by
  intro g
  obtain ⟨h1, h2, h3, h4⟩ := h g
  have e : ((w⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (a • z (F.φ v g) - dY F (mat ρ) (a • Y) (F.φ v g)) * (w : Matrix (Fin n) (Fin n) K) =
      a • (((w⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (z (F.φ v g) - dY F (mat ρ) Y (F.φ v g)) * (w : Matrix (Fin n) (Fin n) K)) := by
    unfold dY
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, ← smul_sub, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨h1, h2, fun i j hij => ?_, fun hg i => ?_⟩
  · rw [e, Matrix.smul_apply, h3 i j hij, smul_zero]
  · rw [e, Matrix.smul_apply, h4 hg i, smul_zero]

private theorem model_coc {l : ℕ} [Fact l.Prime] {n : ℕ} {F : GFrame l} {ρ : F.G₀ →* GL (Fin n) (Qbar l)}
    {P : GL (Fin n) (Qbar l)} {I : F.St → Subgroup F.G₀} {ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ}
    {z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l)} (h : IsOrdCoc F ρ P I ψ z) (a : Qbar l) :
    IsOrdCoc F ρ P I ψ (fun g => a • z g) := by
  refine ⟨h.cont.const_smul a, ?_, ?_, ?_, ?_⟩
  · intro g g'
    rw [h.coc, smul_add, Matrix.mul_smul, Matrix.smul_mul]
  · intro g
    rw [Matrix.mul_smul, h.pol, Matrix.transpose_smul, Matrix.smul_mul, smul_neg]
  · intro u g hg
    rw [h.ine u g hg, smul_zero]
  · intro v
    obtain ⟨w, Y, hw⟩ := h.ord v
    exact ⟨w, a • Y, model_ordAt (F := F) (ψ := ψ v) hw a⟩

theorem UpperTheory.V.Th.Nm.model :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ) (z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l)) (q : ℕ) (sg : Fin q → F.G₀), Continuous ρ → Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤ → F.IsForm c.O n ρ P → ((P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P ∨ (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = -P) → (∀ u, ∀ g ∈ F.Iu u, ρ g = 1) → (∀ v, ∃ g, Function.Injective fun i => ψ v i g) → (∀ v i j, i < j → ψ v i ≠ ψ v j * (F.eps c.O (Qbar l)).comp (F.φ v)) → IsOrdCoc F ρ P F.Iu ψ z → (∀ g, IntM (mat ρ g)) → IntM (P : Matrix (Fin n) (Fin n) (Qbar l)) → IntM ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) → (∀ j, (mat ρ (sg j)).charpoly.Separable) → ∀ c₁ : Coef l, ∃ (c' : Coef l) (y : Pt F c'.O n) (z₀ : F.G₀ → Matrix (Fin n) (Fin n) c'.O) (a : Qbar l) (al : Fin q → Fin n → c'.O), c₁.O ≤ c'.O ∧ IsModel y ρ P ψ ∧ a ≠ 0 ∧ (∀ g, (z₀ g).map (algebraMap c'.O (Qbar l)) = a • z g) ∧ OCoc y z₀ ∧ ∀ j, Function.Injective (al j) ∧ (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i)) := by
  intro l _ n F c ρ P ψ z q sg hc hsp hF hs hI hreg hN hz hρ hP hPi hsep c₁
  choose w₀ Y hw₀ using hz.ord
  choose w hw hwi hwo using fun v => ordInt F ρ v (ψ v) z (w₀ v) (Y v) (hw₀ v)
  choose r hri hrn hrc using fun j => roots _ (hρ (sg j)) (hsep j)
  obtain ⟨c₂, a, h12, ha, hρ₂, hz₂⟩ := repIn F c₁ ρ z hc hρ hz.cont hz.coc
  obtain ⟨b, hb0, hb1, hb⟩ := model_small fun p : F.Vl × Fin n × Fin n => a * Y p.1 p.2.1 p.2.2
  obtain ⟨c₃, h23, k3⟩ := (inOf c₂).1 Unit (fun _ => b) fun _ => hb1
  obtain ⟨c₄, h34, k4⟩ := (inOf c₃).1 _ _ hb
  obtain ⟨c₅, h45, k5⟩ := (inOf c₄).1 (Fin n × Fin n) _ fun p => hP p.1 p.2
  obtain ⟨c₆, h56, k6⟩ := (inOf c₅).1 (Fin n × Fin n) _ fun p => hPi p.1 p.2
  obtain ⟨c₇, h67, k7⟩ := (inOf c₆).1 (F.Vl × Fin n × Fin n) _ fun p => hw p.1 p.2.1 p.2.2
  obtain ⟨c₈, h78, k8⟩ := (inOf c₇).1 (F.Vl × Fin n × Fin n) _ fun p => hwi p.1 p.2.1 p.2.2
  obtain ⟨c', h8, k9⟩ := (inOf c₈).1 (Fin q × Fin n) _ fun p => hrn p.1 p.2
  have h7 := h78.trans h8
  have h6 := h67.trans h7
  have h5 := h56.trans h6
  have h4 := h45.trans h5
  have h3 := h34.trans h4
  have h2 := h23.trans h3
  obtain ⟨y, z₀, hy, hz₀, ho⟩ := mkPt F c c' ρ P ψ (fun g => (b * a) • z g) w (fun v => (b * a) • Y v) hc hsp hF hs hI
    hreg hN (model_coc hz _) (fun v => model_ordAt (hwo v) _) (fun g i j => h2 (hρ₂ g i j)) (fun i j => h5 (k5 (i, j)))
    (fun i j => h6 (k6 (i, j)))
    (fun v => ⟨fun i j => h7 (k7 (v, i, j)), fun i j => h8 (k8 (v, i, j)), fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, mul_assoc]
      exact h4 (k4 (v, i, j))⟩)
    (fun g i j => by
      rw [Matrix.smul_apply, smul_eq_mul, mul_assoc]
      exact mul_mem (h3 (k3 ())) (h2 (hz₂ g i j)))
  refine ⟨c', y, z₀, b * a, fun j i => ⟨r j i, k9 (j, i)⟩, h12.trans h2, hy, mul_ne_zero hb0 ha, hz₀, ho, fun j =>
    ⟨fun i i' h => hri j (congrArg Subtype.val h), ?_⟩⟩
  apply Polynomial.map_injective (algebraMap c'.O (Qbar l)) Subtype.val_injective
  have e : (mat y.ρ (sg j)).map (algebraMap c'.O (Qbar l)) = mat ρ (sg j) := by
    rw [← hy.1]
    rfl
  rw [← Matrix.charpoly_map, e, hrc j, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.PairDual
section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem auxiliaryVectors_pairing_eq_antiDiagonal_gram {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (r : Resid F O n) [IsCO O O] [IsCO O (DualNumber O)] (ρ : F.G₀ →* GL (Fin n) O) (ψ : ∀ v, Fin n → F.Gv v →* Oˣ)
    (ρ' : F.G₀ →* GL (Fin n) (DualNumber O)) (P' : GL (Fin n) (DualNumber O)) (ψ' : ∀ v, Fin n → F.Gv v →* (DualNumber O)ˣ)
    (hn : 1 ≤ n) (hD : (GDet.ofRep (mat ρ)).map (res O O : O →+* ResidueField O) = r.Dbar) (hψ : ∀ v i, r.IsPsi v i (ψ v i))
    (hcont : ∀ i j, AdicCont (maximalIdeal (DualNumber O)) fun g => mat ρ' g i j) (hform : F.IsForm O n ρ' P')
    (hflag : ∀ v, HasFlag (ρ'.comp (F.φ v)) (ψ' v)) (hine : ∀ u, ∀ g ∈ r.Ip u, ρ' g = 1)
    (hρ : pushRep (TrivSqZeroExt.fstHom O O O : DualNumber O →+* O) ρ' = ρ)
    (hψ' : ∀ v i, pushCh (TrivSqZeroExt.fstHom O O O : DualNumber O →+* O) (ψ' v i) = ψ v i ∧
      (AdicCont (maximalIdeal (DualNumber O)) fun g => ((ψ' v i g : (DualNumber O)ˣ) : DualNumber O)) ∧
      ∀ g, g ∈ F.Iv v ∨ g ∈ F.mu v → ((ψ' v i g : (DualNumber O)ˣ) : DualNumber O).snd = 0) :
    ∃ p : Pair r (DualNumber O), p.Maps (TrivSqZeroExt.fstHom O O O : DualNumber O →+* O) (GDet.ofRep (mat ρ)) ψ ∧
      (∀ g, p.D.tr (MonoidAlgebra.single g 1) = (mat ρ' g).trace) ∧
      ∀ v i, ∀ g ∈ F.Iv v, ((p.ψ v i g : (DualNumber O)ˣ) : DualNumber O).snd = 0 := by
  set f : DualNumber O →+* O := (TrivSqZeroExt.fstHom O O O : DualNumber O →+* O) with hf
  have hmap : (GDet.ofRep (mat ρ')).map f = GDet.ofRep (mat ρ) := by
    rw [(CA.d_gmap (GDet.ofRep (mat ρ'))).2.2.2 f (mat ρ'), ← hρ]
    rfl
  have hres : ((res O (DualNumber O) : DualNumber O →ₐ[O] ResidueField O) : DualNumber O →+* ResidueField O) =
      (res O O : O →+* ResidueField O).comp f :=
    RingHom.ext fun x => (res_map (TrivSqZeroExt.fstHom O O O) x).symm
  have hfst : ∀ v i g, f ((ψ' v i g : (DualNumber O)ˣ) : DualNumber O) = ((ψ v i g : Oˣ) : O) := by
    intro v i g
    have := congrArg (fun χ : F.Gv v →* Oˣ => ((χ g : Oˣ) : O)) (hψ' v i).1
    simpa [pushCh] using this
  have hpsi : ∀ v i, r.IsPsi v i (ψ' v i) := by
    intro v i
    refine ⟨(hψ' v i).2.1, fun g => ?_, fun g => ?_⟩
    · have h1 := res_map (TrivSqZeroExt.fstHom O O O) ((ψ' v i g : (DualNumber O)ˣ) : DualNumber O)
      rw [← h1]
      have h2 := hfst v i g
      simp only [hf] at h2
      rw [show (TrivSqZeroExt.fstHom O O O) ((ψ' v i g : (DualNumber O)ˣ) : DualNumber O) = ((ψ v i g : Oˣ) : O) from h2]
      exact (hψ v i).red g
    · have hs := (hψ' v i).2.2 g (Or.inr g.2)
      have h2 := hfst v i g
      have h3 := (hψ v i).mu g
      ext
      · simp only [hf] at h2
        simpa [h3, TrivSqZeroExt.algebraMap_eq_inl] using h2
      · simpa [TrivSqZeroExt.algebraMap_eq_inl] using hs
  have hred : (GDet.ofRep (mat ρ')).map (res O (DualNumber O) : DualNumber O →+* ResidueField O) = r.Dbar := by
    rw [hres, ← (CA.d_gmap (GDet.ofRep (mat ρ'))).2.1, hmap, hD]
  obtain ⟨p, hpD, hpψ⟩ := pairOfRep F O r (DualNumber O) ρ' P' ψ' hn hcont hred hform hpsi hflag hine
  refine ⟨p, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hpD, hmap]
  · intro v i
    rw [hpψ]
    exact (hψ' v i).1
  · intro g
    rw [hpD, (AlgebraTools.Det.repApi (mat ρ')).2.2.1 hn (MonoidAlgebra.single g 1)]
    simp [GDet.repAlg]
  · intro v i g hg
    rw [hpψ]
    exact (hψ' v i).2.2 g (Or.inl hg)

theorem UpperTheory.V.Th.Nm.pairDual :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (r : Resid F c.O n) (y : Pt (reIu F r.Ip) c.O n) (z : F.G₀ → Matrix (Fin n) (Fin n) c.O) [IsCO c.O c.O] [IsCO c.O (DualNumber c.O)], 1 ≤ n → OCoc y z → (GDet.ofRep (mat y.ρ)).map (res c.O c.O : c.O →+* ResidueField c.O) = r.Dbar → (∀ v i, r.IsPsi v i (y.ψ v i)) → ∃ p : Pair r (DualNumber c.O), p.Maps (TrivSqZeroExt.fstHom c.O c.O c.O : DualNumber c.O →+* c.O) (GDet.ofRep (mat y.ρ)) y.ψ ∧ (∀ g, (p.D.tr (MonoidAlgebra.single g 1)).snd = (z g * mat y.ρ g).trace) ∧ ∀ v i, ∀ g ∈ F.Iv v, ((p.ψ v i g : (DualNumber c.O)ˣ) : DualNumber c.O).snd = 0 := by
  intro l _ n F c r y z _ _ hn hz hD hψ
  obtain ⟨ρ', P', ψ', hcont, hform, hflag, hine, hρ, htr, hψ'⟩ := dualRep (reIu F r.Ip) c y z hz
  obtain ⟨p, h1, h2, h3⟩ := auxiliaryVectors_pairing_eq_antiDiagonal_gram F c.O r y.ρ y.ψ ρ' P' ψ' hn hD hψ hcont hform hflag hine hρ hψ'
  exact ⟨p, h1, fun g => (congrArg TrivSqZeroExt.snd (h2 g)).trans (htr g), h3⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.SelfDual
section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

namespace UpperTheory.V.Th.Nm

private theorem sd_norm {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) : ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  haveI := c.fin
  have hx : IsIntegral ℤ_[l] (x : PadicAlgCl l) := (Algebra.IsIntegral.isIntegral x).map c.O.val
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hx,
    spectralValue_le_one_iff ((minpoly.monic hx).map _)]
  intro n
  rw [Polynomial.coeff_map]
  exact ((minpoly ℤ_[l] (x : PadicAlgCl l)).coeff n).2

private theorem sd_eps {l : ℕ} [Fact l.Prime] (F : GFrame l) (c : Coef l) (g : F.G₀) (z : ℤ) :
    ‖((F.eps c.O (Qbar l) g ^ z : (Qbar l)ˣ) : Qbar l)‖ ≤ 1 := by
  have h1 : ‖((F.eps c.O (Qbar l) g : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
    simp only [GFrame.eps, pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.coe_comp,
      Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact (PadicAlgCl.norm_extends l _).trans (PadicInt.norm_units _)
  rw [Units.val_zpow_eq_zpow_val, norm_zpow, h1, _root_.one_zpow]

private theorem sd_conj_conj {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) : F.conj (F.conj g) = g := by
  apply Subtype.ext
  show F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = g
  rw [inv_eq_of_mul_eq_one_right F.c_sq, mul_assoc, mul_assoc, mul_assoc, F.c_sq, mul_one, ← mul_assoc, F.c_sq, one_mul]

private theorem sd_sgn {K : Type} [CommRing K] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) K) (h : Pᵀ = P ∨ Pᵀ = -P) :
    (Qᵀ * P * Q)ᵀ = Qᵀ * P * Q ∨ (Qᵀ * P * Q)ᵀ = -(Qᵀ * P * Q) := by
  have e : (Qᵀ * P * Q)ᵀ = Qᵀ * Pᵀ * Q := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rcases h with h | h
  · left
    rw [e, h]
  · right
    rw [e, h, Matrix.mul_neg, Matrix.neg_mul]

private theorem sd_form {K : Type} [CommRing K] {n : ℕ} (A B P Q P₀ : GL (Fin n) K) (e : K)
    (hP : (P₀ : Matrix (Fin n) (Fin n) K) = (Q : Matrix (Fin n) (Fin n) K)ᵀ * P * Q)
    (h : (A : Matrix (Fin n) (Fin n) K)ᵀ * P * B = e • (P : Matrix (Fin n) (Fin n) K)) :
    ((P₀ * (Q⁻¹ * B * Q) * P₀⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      e • ((Q⁻¹ * A⁻¹ * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ := by
  have hPB : (P : Matrix (Fin n) (Fin n) K) * B = e • ((↑A⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * P) := by
    calc (P : Matrix (Fin n) (Fin n) K) * B
        = ((↑A⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * (A : Matrix (Fin n) (Fin n) K)ᵀ) * P * B := by
          rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
      _ = (↑A⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * ((A : Matrix (Fin n) (Fin n) K)ᵀ * P * B) := by
          simp only [Matrix.mul_assoc]
      _ = e • ((↑A⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * P) := by
          rw [h, Matrix.mul_smul]
  have hQ : ∀ X : Matrix (Fin n) (Fin n) K,
      (↑Q⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * ((Q : Matrix (Fin n) (Fin n) K)ᵀ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
  have key : (P₀ : Matrix (Fin n) (Fin n) K) *
      ((↑Q⁻¹ : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) * (Q : Matrix (Fin n) (Fin n) K)) =
      (e • ((↑Q⁻¹ : Matrix (Fin n) (Fin n) K) * (↑A⁻¹ : Matrix (Fin n) (Fin n) K) *
        (Q : Matrix (Fin n) (Fin n) K))ᵀ) * (P₀ : Matrix (Fin n) (Fin n) K) := by
    rw [hP, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left, hQ]
    rw [← Matrix.mul_assoc (P : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin n) (Fin n) K), hPB]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  simp only [Units.val_mul]
  rw [key, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

end UpperTheory.V.Th.Nm

theorem UpperTheory.V.Th.Nm.selfDual :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)), Continuous ρ → Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤ → F.IsForm c.O n ρ P → ∃ Q P' : GL (Fin n) (Qbar l), (P' : Matrix (Fin n) (Fin n) (Qbar l)) = (Q : Matrix (Fin n) (Fin n) (Qbar l))ᵀ * P * Q ∧ ((P' : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P' ∨ (P' : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = -P') ∧ IntM (P' : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((P'⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ ∀ g, IntM (mat (cj Q ρ) g) := by
  intro l hl n F c ρ P hρ hspan hform
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  obtain ⟨c', Q₀, ρ₀, -, hQ₀, -⟩ := Ws.Eb.intModel c ρ hρ
  have hint : ∀ g, IntM ((cj Q₀ ρ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    intro g i j
    rw [cj_apply, mul_assoc, hQ₀ g, inv_mul_cancel_left]
    exact sd_norm c' ((ρ₀ g : Matrix (Fin n) (Fin n) c'.O) i j)
  let Qt : GL (Fin n) (Qbar l) :=
    ⟨(Q₀ : Matrix (Fin n) (Fin n) (Qbar l))ᵀ, (↑Q₀⁻¹ : Matrix (Fin n) (Fin n) (Qbar l))ᵀ,
      by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
      by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩
  obtain ⟨P₁, hP₁⟩ : ∃ P₁ : GL (Fin n) (Qbar l),
      (P₁ : Matrix (Fin n) (Fin n) (Qbar l)) = (Q₀ : Matrix (Fin n) (Fin n) (Qbar l))ᵀ * P * Q₀ :=
    ⟨Qt * P * Q₀, rfl⟩
  have hsP₁ : (P₁ : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P₁ ∨
      (P₁ : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = -(P₁ : Matrix (Fin n) (Fin n) (Qbar l)) := by
    rw [hP₁]
    exact sd_sgn _ _ (sign F c ρ P hspan hform)
  have hconj : ∀ g, IntM ((P₁ * cj Q₀ ρ (F.conj g) * P₁⁻¹ : GL (Fin n) (Qbar l)) :
      Matrix (Fin n) (Fin n) (Qbar l)) := by
    intro g
    have key := sd_form (ρ g) (ρ (F.conj g)) P Q₀ P₁ _ hP₁ (hform g)
    rw [cj_apply, key]
    intro i j
    have hinv : (Q₀⁻¹ * (ρ g)⁻¹ * Q₀ : GL (Fin n) (Qbar l)) = cj Q₀ ρ g⁻¹ := by
      rw [cj_apply, map_inv]
    rw [hinv, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, norm_mul]
    exact mul_le_one₀ (sd_eps F c g _) (norm_nonneg _) (hint _ j i)
  obtain ⟨Q₂, P', hP', hP'int, hP'inv, hQ₂⟩ := midpoint (Set.range (cj Q₀ ρ)) P₁ hsP₁ (by
    rintro _ ⟨h, rfl⟩
    refine ⟨hint h, ?_⟩
    have := hconj (F.conj h)
    rwa [sd_conj_conj] at this)
  refine ⟨Q₀ * Q₂, P', ?_, ?_, hP'int, hP'inv, ?_⟩
  · rw [hP', hP₁]
    simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  · rw [hP']
    exact sd_sgn _ _ hsP₁
  · intro g
    have := hQ₂ _ ⟨g, rfl⟩
    rw [cj_apply] at this
    show IntM ((cj (Q₀ * Q₂) ρ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))
    rw [cj_apply, _root_.mul_inv_rev]
    simpa only [mul_assoc] using this
end

