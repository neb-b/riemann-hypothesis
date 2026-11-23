module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.BarOne
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem tri_mul {X : Type} [CommRing X] {n : ℕ} (M N : Matrix (Fin n) (Fin n) X)
    (hM : ∀ i j, j < i → M i j = 0) (hN : ∀ i j, j < i → N i j = 0) :
    (∀ i j, j < i → (M * N) i j = 0) ∧ ∀ i, M i i = 0 → (M * N) i i = 0 := by
  constructor
  · intro i j hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · rw [hM i k hk, zero_mul]
    · rw [hN k j (lt_of_lt_of_le hij hk), mul_zero]
  · intro i hi
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_trichotomy k i with hk | rfl | hk
    · rw [hM i k hk, zero_mul]
    · rw [hi, zero_mul]
    · rw [hN k i hk, mul_zero]

private theorem conj_id {O A : Type} [CommRing O] [Ring A] [Algebra O A] (c : O) (W Wi P Pi d Y : A)
    (h1 : Wi * W = 1) (h2 : W * Wi = 1) (h3 : P * Pi = 1) :
    Wi * (c • (d * Pi) - (P * (W * Y * Wi) * Pi - W * Y * Wi)) * W =
      (c • (Wi * d * W) - ((Wi * P * W) * Y - Y * (Wi * P * W))) * (Wi * Pi * W) := by
  have e1 : ∀ Z : A, W * (Wi * Z) = Z := fun Z => by rw [← mul_assoc, h2, one_mul]
  have e2 : ∀ Z : A, Wi * (W * Z) = Z := fun Z => by rw [← mul_assoc, h1, one_mul]
  have e3 : ∀ Z : A, P * (Pi * Z) = Z := fun Z => by rw [← mul_assoc, h3, one_mul]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, e1, e2, e3, h1, h2, h3, mul_one]

theorem UpperTheory.V.Th.Coc.locAt :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G0 : Glob l L} {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [Algebra ℤ_[l] O] (y : Pt G0.frame O n) (v : L.Vl), ∃ c₁ : O, c₁ ≠ 0 ∧ ∀ (G : Glob l L) (h : G.Hom G0) (R : Type) [CommRing R] [Algebra O R] (x : R →ₐ[O] O) (m : ℕ) (δ : R →ₗ[O] Om O m) (τ : MonoidAlgebra R G.G₀ → R) (c : O) (d : MonoidAlgebra R G.G₀ →+ Matrix (Fin n) (Fin n) (Om O m)) (ψ : Fin n → L.Gv v →* Rˣ), IsLift x δ (repR x (mat (y.ρ.comp h.p₀))) τ c d → (∀ i g, x (ψ i g : Rˣ) = (y.ψ v i g : Oˣ)) → (∀ g, repR x (mat (y.ρ.comp h.p₀)) (G.frame.oEl v ψ g) = 0 ∧ d (G.frame.oEl v ψ g) = 0) → (∀ i, ∀ g ∈ G.frame.mu v, δ (ψ i g : Rˣ) = 0) → ∃ Y, LocAt G.frame (y.ρm h m) (fun v => red m (y.w v)) (fun v => red m ((y.w v)⁻¹ : GL (Fin n) O)) (fun g => c₁ • (d (MonoidAlgebra.single g 1) * y.ρm h m g⁻¹)) v Y := by
  intro l _ L G0 n O _ _ _ _ y v
  obtain ⟨s, hs⟩ := y.reg v
  let r : L.Gv v → Matrix (Fin n) (Fin n) O := fun g =>
    (((y.w v)⁻¹ * y.ρ (G0.frame.φ v g) * y.w v : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)
  obtain ⟨c₁, hc₁, hfl⟩ := flag r (fun i g => ((y.ψ v i g : Oˣ) : O)) s
    (fun g => (y.tri v g).1) (fun g => (y.tri v g).2) (fun i j hij => hs (Units.ext hij))
  refine ⟨c₁, hc₁, ?_⟩
  intro G h R _ _ x m δ τ c d ψ hlift hψ hker hmu
  let W : GL (Fin n) O := y.w v
  let ρg : G.G₀ →* Matrix (Fin n) (Fin n) O := mat (y.ρ.comp h.p₀)
  let ρg' : G.G₀ →* Matrix (Fin n) (Fin n) O := mat ((MulAut.conj W⁻¹).toMonoidHom.comp (y.ρ.comp h.p₀))
  have hconj : ∀ a, repR x ρg' a = ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * repR x ρg a * ((W⁻¹⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := by
    intro a
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, mul_add, add_mul]
    | single g a =>
      rw [repR_single, repR_single, inv_inv, mul_smul_comm, smul_mul_assoc]
      rfl
  obtain ⟨d', hl', hd'⟩ := liftConj x δ (repR x ρg') (repR x ρg) τ c W⁻¹ d hconj hlift
  have hp : ∀ g : L.Gv v, h.p₀ (G.frame.φ v g) = G0.frame.φ v g := fun g => Subtype.ext (h.φ v g)
  have hr : ∀ g, ρg' (G.frame.φ v g) = r g := by
    intro g
    simp only [ρg', r, mat, MonoidHom.comp_apply, hp, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rfl
  have hD : ∀ gt : Fin n → L.Gv v, (List.ofFn fun i => dualM (bar (Om O m) (r (gt i))) (d' (MonoidAlgebra.single (G.frame.φ v (gt i)) 1)) - (TrivSqZeroExt.inl (algebraMap O (Om O m) ((y.ψ v i (gt i) : Oˣ) : O)) + TrivSqZeroExt.inr (c • δ ((ψ i (gt i) : Rˣ) : R))) • 1).prod = 0 := by
    intro gt
    have e := rel x δ ρg' τ c d' (fun g : L.Gv v => G.frame.φ v g) (fun i g => ((ψ i g : Rˣ) : R)) gt hl' ?_ ?_
    · simpa only [hr, hψ] using e
    · rw [hconj]
      show _ * repR x ρg (G.frame.oEl v ψ gt) * _ = 0
      rw [(hker gt).1, mul_zero, zero_mul]
    · rw [hd']
      show _ * d (G.frame.oEl v ψ gt) * _ = 0
      rw [(hker gt).2, mul_zero, zero_mul]
  obtain ⟨Y', hY'⟩ := hfl (Om O m) (fun g => d' (MonoidAlgebra.single (G.frame.φ v g) 1)) (fun i g => c • δ ((ψ i g : Rˣ) : R)) hD
  have hredm : ∀ A B : Matrix (Fin n) (Fin n) O, red m (A * B) = red m A * red m B := fun A B => Matrix.map_mul
  have hred1 : red m (1 : Matrix (Fin n) (Fin n) O) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hbar : ∀ Z : Matrix (Fin n) (Fin n) O, bar (Om O m) Z = red m Z := fun Z => rfl
  have h1 : red m ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * red m (W : Matrix (Fin n) (Fin n) O) = 1 := by
    rw [← hredm, ← Units.val_mul, inv_mul_cancel, Units.val_one, hred1]
  have h2 : red m (W : Matrix (Fin n) (Fin n) O) * red m ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = 1 := by
    rw [← hredm, ← Units.val_mul, mul_inv_cancel, Units.val_one, hred1]
  have hd'' : ∀ a, red m ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * d a * red m (W : Matrix (Fin n) (Fin n) O) = d' a := by
    intro a
    rw [hd', inv_inv]
    rfl
  have hPr : ∀ g : G.G₀, ∀ g0 : L.Gv v, h.p₀ g = G0.frame.φ v g0 →
      red m ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * y.ρm h m g * red m (W : Matrix (Fin n) (Fin n) O) = bar (Om O m) (r g0) := by
    intro g g0 hg
    rw [hbar]
    show red m _ * red m _ * red m _ = red m _
    rw [← hredm, ← hredm]
    congr 1
    show ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * ((y.ρ (h.p₀ g) : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (W : Matrix (Fin n) (Fin n) O) = _
    rw [hg]
    simp only [r, W, Units.val_mul]
  refine ⟨red m (W : Matrix (Fin n) (Fin n) O) * Y' * red m ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O), fun g => ?_⟩
  have h3 : y.ρm h m (G.frame.φ v g) * y.ρm h m (G.frame.φ v g)⁻¹ = 1 := by
    show red m _ * red m _ = 1
    rw [← hredm, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, hred1]
  simp only [UpperTheory.V.Pa.dY]
  rw [conj_id c₁ _ _ _ _ _ Y' h1 h2 h3, hd'', hPr _ g (hp g), hPr _ g⁻¹ (by rw [map_inv, hp, map_inv])]
  have hN : ∀ i j, j < i → bar (Om O m) (r g⁻¹) i j = 0 := by
    intro i j hij
    show algebraMap O (Om O m) (r g⁻¹ i j) = 0
    rw [show r g⁻¹ i j = 0 from (y.tri v g⁻¹).1 i j hij, map_zero]
  have T := tri_mul _ _ (hY' g).1 hN
  refine ⟨T.1, fun hg i => T.2 i ?_⟩
  rw [(hY' g).2 i, hmu i g hg, smul_zero, smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.ConjHom
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private def conjHom {O : Type} [CommRing O] {n : ℕ} (Q : GL (Fin n) O) :
    Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) O where
  toFun Z := ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * Z * (Q : Matrix (Fin n) (Fin n) O)
  map_one' := by rw [Matrix.mul_one, Units.inv_mul]
  map_mul' a b := by
    simp only [Matrix.mul_assoc]
    rw [Units.mul_inv_cancel_left]
  map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul]
  map_add' a b := by rw [Matrix.mul_add, Matrix.add_mul]

theorem UpperTheory.V.Th.Coc.liftG :
    ∀ {n : ℕ} {O R X G : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [CommRing X] [Algebra O X] [Group G] (D : GDet n R G) (χ : Fin n → G →* (ResidueField O)ˣ) (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : G →* Matrix (Fin n) (Fin n) O) (c₀ : O), 1 ≤ n → Function.Injective χ → D.map (res O R : R →+* ResidueField O) = GDet.ofRep (diagRep χ) → D.map x.toRingHom = GDet.ofRep ρ → c₀ ≠ 0 → (∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) → IsDer x δ → ∃ d : MonoidAlgebra R G →+ Matrix (Fin n) (Fin n) X, IsLift x δ (repR x ρ) D.tr (c₀ ^ (2 * n) * c₀ ^ (2 * n)) d := by
  intro n O R X G _ _ _ _ _ _ _ _ _ D χ x δ ρ c₀ hn hχ hres hx hc hspan hδ
  obtain ⟨E, _, _, π, τ, e, hπ, hτ, hg⟩ := UpperTheory.V.Th.Coc.gma (O := O) D χ hn hχ hres
  obtain ⟨htr, hsm, -⟩ := UpperTheory.V.Th.Coc.trRep D x ρ hn hx
  obtain ⟨k1, -⟩ := UpperTheory.V.Th.Coc.kill0 ρ c₀ hc hspan
  have hs : ∀ g, repR x ρ (MonoidAlgebra.single g (1 : R)) = ρ g := fun g => by
    rw [repR_single, map_one, one_smul]
  have hker : RingHom.ker π.toRingHom ≤ RingHom.ker (repR x ρ) := by
    intro y hy
    have hy' : π y = 0 := hy
    refine k1 _ fun g => ?_
    have h := htr (MonoidAlgebra.single g 1 * y)
    rw [map_mul, hs, ← hτ, map_mul, hy', mul_zero, map_zero, map_zero] at h
    exact h
  obtain ⟨ρE, hρE⟩ : ∃ ρE : E →+* Matrix (Fin n) (Fin n) O, ∀ y, ρE (π y) = repR x ρ y :=
    ⟨π.toRingHom.liftOfSurjective hπ ⟨repR x ρ, hker⟩, fun y =>
      π.toRingHom.liftOfRightInverse_comp_apply _ _ ⟨repR x ρ, hker⟩ y⟩
  have htrE : ∀ a, (ρE a).trace = x (τ a) := fun a => by
    obtain ⟨y, rfl⟩ := hπ a
    rw [hρE, htr, hτ]
  have hsmE : ∀ (r : R) a, ρE (r • a) = x r • ρE a := fun r a => by
    obtain ⟨y, rfl⟩ := hπ a
    rw [← map_smul π, hρE, hρE, hsm]
  have hrange : ∀ Z ∈ Submodule.span O (Set.range ρ), ∃ a, ρE a = Z := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ =>
      obtain ⟨g, rfl⟩ := hZ
      exact ⟨π (MonoidAlgebra.single g 1), by rw [hρE, hs]⟩
    | zero => exact ⟨0, map_zero _⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', map_add _ _ _⟩
    | smul o a _ ha =>
      obtain ⟨a', rfl⟩ := ha
      exact ⟨algebraMap O R o • a', by rw [hsmE, AlgHom.commutes]; rfl⟩
  obtain ⟨Q, hQ⟩ := UpperTheory.V.Th.Coc.idemDiag (fun i => ρE (e i)) (hg.idem.map ρE)
    (fun i => by rw [htrE, hg.one, map_one])
  let ρ' : E →+* Matrix (Fin n) (Fin n) O := (conjHom Q).comp ρE
  have hρ' : ∀ a, ρ' a = ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * ρE a * (Q : Matrix (Fin n) (Fin n) O) :=
    fun a => rfl
  have htr' : ∀ a, (ρ' a).trace = x (τ a) := fun a => by
    rw [hρ', Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, htrE]
  have hsm' : ∀ (r : R) a, ρ' (r • a) = x r • ρ' a := fun r a => by
    rw [hρ', hρ', hsmE, Matrix.mul_smul, Matrix.smul_mul]
  have hsurj' : ∀ Z, ∃ a, ρ' a = c₀ • Z := fun Z => by
    obtain ⟨a, ha⟩ := hrange _ (hspan ((Q : Matrix (Fin n) (Fin n) O) * Z *
      ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)))
    refine ⟨a, ?_⟩
    rw [hρ', ha, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
    rw [Units.inv_mul_cancel_left, Units.inv_mul, Matrix.mul_one]
  obtain ⟨s, β, hβ, h1, h2, h3⟩ := UpperTheory.V.Th.Coc.smat x ρ' τ e c₀ hn hg hQ htr' hsurj'
  obtain ⟨d, hd⟩ := UpperTheory.V.Th.Coc.liftOfS x δ ρ' τ s β (c₀ ^ (2 * n)) hδ hsm' htr' hβ h1 h2 h3
  obtain ⟨d', hd', -⟩ := UpperTheory.V.Th.Coc.liftConj x δ ρE ρ' τ _ Q d (fun a => by
    rw [hρ']
    simp only [Matrix.mul_assoc]
    rw [Units.mul_inv_cancel_left, Units.mul_inv, Matrix.mul_one]) hd
  refine ⟨d'.comp π.toRingHom.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro a b
    have h := hd'.mul (π a) (π b)
    rw [← map_mul, hρE, hρE] at h
    exact h
  · intro r a
    have h := hd'.smul r (π a)
    rw [← map_smul π, hρE] at h
    exact h
  · intro a
    have h := hd'.tr (π a)
    rw [hτ] at h
    exact h
end

