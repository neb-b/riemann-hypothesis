module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0011
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0010

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianFormsIntegrallyEquivalentAlmostAll
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GoodIso

theorem exists_gl_to_one (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A)
    (hσ : ∀ y, σ (σ y) = y) (h2 : IsUnit (2 : A)) (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ)
    (hN : ∀ β : A, IsUnit β → σ β = β → ∃ a : A, a * σ a = β)
    (m : ℕ) (J : Matrix (Fin m) (Fin m) A) (hJ : ∀ i j, σ (J j i) = J i j) (hd : IsUnit J.det) :
    ∃ h : GL (Fin m) A,
      cT σ (h : Matrix (Fin m) (Fin m) A) * J * (h : Matrix (Fin m) (Fin m) A) = 1 := by
  obtain ⟨g, d, hg, hdd, hgJ⟩ := _root_.GlobalTheory.CompanionTheory.SW.RingDiag.diagonalise A σ hσ
    (fun m J hJ hu => _root_.GlobalTheory.CompanionTheory.SW.UnitRep.exists_isUnit_hform A σ hσ h2 hδ m J hJ hu) m J hJ hd
  choose a ha using fun i => hN (d i) (hdd i).1 (hdd i).2
  have hau : ∀ i, IsUnit (a i) := fun i =>
    isUnit_of_mul_isUnit_left (y := σ (a i)) (by rw [ha i]; exact (hdd i).1)
  choose c hc using fun i => (hau i).exists_right_inv
  have hcu : ∀ i, IsUnit (c i) := fun i => IsUnit.of_mul_eq_one (a i) (by rw [mul_comm]; exact hc i)
  have hdet : IsUnit (g * Matrix.diagonal c).det := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    exact hg.mul (IsUnit.prod_univ_iff.2 hcu)
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit, ?_⟩
  rw [IsUnit.unit_spec, cT_mul]
  have hD : cT σ (Matrix.diagonal c) = Matrix.diagonal (fun i => σ (c i)) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [cT]
    · simp [cT, Matrix.diagonal_apply, hij, Ne.symm hij]
  calc cT σ (Matrix.diagonal c) * cT σ g * J * (g * Matrix.diagonal c)
      = cT σ (Matrix.diagonal c) * (cT σ g * J * g) * Matrix.diagonal c := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hgJ, hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        have h1 : σ (c i) * σ (a i) = 1 := by rw [← map_mul, mul_comm, hc i, map_one]
        rw [← ha i]
        calc σ (c i) * (a i * σ (a i)) * c i = (σ (c i) * σ (a i)) * (a i * c i) := by ring
          _ = 1 := by rw [h1, hc i, one_mul]

theorem exists_gl_equiv (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A)
    (hσ : ∀ y, σ (σ y) = y) (h2 : IsUnit (2 : A)) (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ)
    (hN : ∀ β : A, IsUnit β → σ β = β → ∃ a : A, a * σ a = β)
    (m : ℕ) (J J' : Matrix (Fin m) (Fin m) A) (hJ : ∀ i j, σ (J j i) = J i j) (hd : IsUnit J.det)
    (hJ' : ∀ i j, σ (J' j i) = J' i j) (hd' : IsUnit J'.det) :
    ∃ G : GL (Fin m) A,
      J' = cT σ (G : Matrix (Fin m) (Fin m) A) * J * (G : Matrix (Fin m) (Fin m) A) := by
  obtain ⟨h, hh⟩ := exists_gl_to_one A σ hσ h2 hδ hN m J hJ hd
  obtain ⟨k, hk⟩ := exists_gl_to_one A σ hσ h2 hδ hN m J' hJ' hd'
  refine ⟨h * k⁻¹, ?_⟩
  have hkk : (k : Matrix (Fin m) (Fin m) A) * ((k⁻¹ : GL (Fin m) A) : Matrix (Fin m) (Fin m) A) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hck : cT σ ((k⁻¹ : GL (Fin m) A) : Matrix (Fin m) (Fin m) A) * cT σ (k : Matrix (Fin m) (Fin m) A) = 1 := by
    rw [← cT_mul, hkk, cT_one]
  set K : Matrix (Fin m) (Fin m) A := (k : Matrix (Fin m) (Fin m) A)
  set L : Matrix (Fin m) (Fin m) A := ((k⁻¹ : GL (Fin m) A) : Matrix (Fin m) (Fin m) A)
  set H : Matrix (Fin m) (Fin m) A := (h : Matrix (Fin m) (Fin m) A)
  have e1 : J' = cT σ L * (cT σ K * J' * K) * L := by
    calc J' = (cT σ L * cT σ K) * J' * (K * L) := by rw [hck, hkk, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have e2 : cT σ (H * L) * J * (H * L) = cT σ L * (cT σ H * J * H) * L := by
    rw [cT_mul]; simp only [Matrix.mul_assoc]
  rw [Units.val_mul]
  change J' = cT σ (H * L) * J * (H * L)
  rw [e2, hh, ← hk, ← e1]

theorem exists_gl_sub {R : Type} [CommRing R] (s : R →+* R) (hs : ∀ y, s (s y) = y) (O : Subring R)
    (hO : ∀ y ∈ O, s y ∈ O) [Finite (MaximalSpectrum O)] (h2 : IsUnit (2 : O))
    (hδ : ∃ δ : O, IsUnit δ ∧ s (δ : R) = -(δ : R))
    (hN : ∀ β : O, IsUnit β → s (β : R) = β → ∃ a : O, (a : R) * s a = β)
    (m : ℕ) (K K' : Matrix (Fin m) (Fin m) R)
    (hK : ∀ i j, s (K j i) = K i j) (hK' : ∀ i j, s (K' j i) = K' i j)
    (iK : ∀ i j, K i j ∈ O) (iK' : ∀ i j, K' i j ∈ O)
    (wK : ∃ w ∈ O, K.det * w = 1) (wK' : ∃ w ∈ O, K'.det * w = 1) :
    ∃ g : GL (Fin m) R, K' = cT s (g : Matrix (Fin m) (Fin m) R) * K * (g : Matrix (Fin m) (Fin m) R) ∧
      (∀ i j, (g : Matrix (Fin m) (Fin m) R) i j ∈ O) ∧
      ∀ i j, ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) i j ∈ O := by
  let σO : O →+* O := (s.comp O.subtype).codRestrict O (fun y => hO y y.2)
  have hσO : ∀ y : O, ((σO y : O) : R) = s (y : R) := fun y => rfl
  have lift : ∀ (P : Matrix (Fin m) (Fin m) R) (iP : ∀ i j, P i j ∈ O), (∃ w ∈ O, P.det * w = 1) →
      ∃ Q : Matrix (Fin m) (Fin m) O, Q.map O.subtype = P ∧ IsUnit Q.det := by
    intro P iP ⟨w, hw, hPw⟩
    refine ⟨Matrix.of fun i j => ⟨P i j, iP i j⟩, by ext i j; rfl, ?_⟩
    have hdet : ((Matrix.of fun i j => (⟨P i j, iP i j⟩ : O)).det : O).1 = P.det := by
      have := RingHom.map_det O.subtype (Matrix.of fun i j => (⟨P i j, iP i j⟩ : O))
      exact this
    refine IsUnit.of_mul_eq_one ⟨w, hw⟩ (Subtype.ext ?_)
    simpa [hdet] using hPw
  obtain ⟨Q, rfl, uQ⟩ := lift K iK wK
  obtain ⟨Q', rfl, uQ'⟩ := lift K' iK' wK'
  have herm : ∀ (Q : Matrix (Fin m) (Fin m) O), (∀ i j, s ((Q.map O.subtype) j i) = (Q.map O.subtype) i j) →
      ∀ i j, σO (Q j i) = Q i j := fun Q h i j => Subtype.ext (h i j)
  obtain ⟨G, hG⟩ := exists_gl_equiv O σO (fun y => Subtype.ext (hs _)) h2
    (by obtain ⟨δ, h1, h3⟩ := hδ; exact ⟨δ, h1, Subtype.ext h3⟩)
    (fun β hβ hβ' => by
      obtain ⟨a, ha⟩ := hN β hβ (congrArg Subtype.val hβ')
      exact ⟨a, Subtype.ext ha⟩)
    m Q Q' (herm Q hK) uQ (herm Q' hK') uQ'
  have hcT : ∀ P : Matrix (Fin m) (Fin m) O,
      cT s (P.map O.subtype) = (cT σO P).map O.subtype := fun P => by ext i j; rfl
  refine ⟨bc O.subtype G, ?_, ?_, ?_⟩
  · have hv : ((bc O.subtype G : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) =
        (G : Matrix (Fin m) (Fin m) O).map O.subtype := rfl
    rw [hv, hcT, hG, Matrix.map_mul, Matrix.map_mul]
  · intro i j
    exact (G.val i j).2
  · intro i j
    rw [← map_inv]
    exact ((G⁻¹).val i j).2

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2]
  simp

theorem sigR_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (h : ∀ x, σ (σ x) = x) (y : R ⊗[F] E) : sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, h]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem mulVec_mem {R : Type} [CommRing R] (O : Subring R) {m : ℕ} (P : Matrix (Fin m) (Fin m) R)
    (hP : ∀ i j, P i j ∈ O) (x : Fin m → R) (hx : ∀ i, x i ∈ O) (i : Fin m) : P.mulVec x i ∈ O := by
  change ∑ j, P i j * x j ∈ O
  exact O.sum_mem fun j _ => O.mul_mem (hP i j) (hx j)

theorem good_iso : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ g : GL (Fin M) (Fv F v ⊗[F] E), JR (Fv F v) J' = cT (sigR (Fv F v) σ) (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) * JR (Fv F v) J * (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) ∧ ∀ (n : ℕ) (X : Fin n → Fin M → Fv F v ⊗[F] E), actTup (Fv F v) g X ∈ latV b v ↔ X ∈ latV b v := by
  intro F E _ _ _ _ _ σ hCM M J hJ J' hJ' d b
  have h1 := (_root_.GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ hCM d b).1
  have ent : ∀ P : Matrix (Fin M) (Fin M) E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (F := F) (Fv F v) (P i j)) k ∈
        v.adicCompletionIntegers F := fun P =>
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => h1 (P i j)
  filter_upwards [_root_.GlobalTheory.CompanionTheory.SW.GoodRing.good_ring F E σ hCM d b, ent J, ent J', h1 (J.det)⁻¹, h1 (J'.det)⁻¹]
    with v hv eJ eJ' dJ dJ'
  obtain ⟨O, hmem, hst, hfin, h2, hδ, -, hN⟩ := hv
  have wit : ∀ P : Matrix (Fin M) (Fin M) E, P.det ≠ 0 →
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (F := F) (Fv F v) (P.det)⁻¹) k ∈
        v.adicCompletionIntegers F) → ∃ w ∈ O, (JR (Fv F v) P).det * w = 1 := by
    intro P hP hk
    refine ⟨inclR (F := F) (Fv F v) (P.det)⁻¹, (hmem _).2 hk, ?_⟩
    have : (JR (Fv F v) P).det = inclR (F := F) (Fv F v) P.det := (RingHom.map_det (inclR (F := F) (Fv F v)) P).symm
    rw [this, ← map_mul, mul_inv_cancel₀ hP, map_one]
  obtain ⟨g, hg, ig, ig'⟩ := exists_gl_sub (sigR (Fv F v) σ)
    (sigR_sigR (Fv F v) σ (sigma_sigma σ hCM)) O hst h2 hδ hN M (JR (Fv F v) J) (JR (Fv F v) J')
    (map_mem_HermR (Fv F v) σ J hJ.1) (map_mem_HermR (Fv F v) σ J' hJ'.1)
    (fun i j => (hmem _).2 (eJ i j)) (fun i j => (hmem _).2 (eJ' i j))
    (wit J hJ.2 dJ) (wit J' hJ'.2 dJ')
  refine ⟨g, hg, fun n X => ?_⟩
  have lat : ∀ Y : Fin n → Fin M → Fv F v ⊗[F] E, Y ∈ latV b v ↔ ∀ a i, Y a i ∈ O := fun Y =>
    ⟨fun h a i => (hmem _).2 (h a i), fun h a i => (hmem _).1 (h a i)⟩
  rw [lat, lat]
  constructor
  · intro h a i
    have e : X a = ((g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)).mulVec
        (actTup (Fv F v) g X a) := by
      simp only [actTup, Matrix.mulVec_mulVec]
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e]
    exact mulVec_mem O _ ig' _ (h a) i
  · intro h a i
    exact mulVec_mem O _ ig _ (h a) i

end GlobalTheory.CompanionTheory.SW.GoodIso
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeGramScalarAlmostAll
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GoodTrans

theorem transit_ring {T : Type} [CommRing T] (O : Subring T) (s : T →+* T)
    (hs : ∀ y ∈ O, s y ∈ O) (hss : ∀ y, s (s y) = y) {M : ℕ} (JT : Matrix (Fin M) (Fin M) T)
    (hJO : ∀ i j, JT i j ∈ O) (hJ : ∀ i j, s (JT j i) = JT i j) (x y : Fin M → T)
    (hx : ∀ i, x i ∈ O) (hy : ∀ i, y i ∈ O) (hxy : hform s JT x x = hform s JT y y)
    (w : T) (hw : w ∈ O) (hxw : hform s JT x x * w = 1)
    (hgood : ∀ p β : O, IsUnit β → s β = β → ∃ ε z : O,
      (ε : T) * s ε = 1 ∧ ((β : T) - s ε * p) * z = 1) :
    ∃ g ∈ UJ s JT, (g : Matrix (Fin M) (Fin M) T) *ᵥ x = y ∧
      (∀ i j, (g : Matrix (Fin M) (Fin M) T) i j ∈ O) ∧
      ∀ i j, ((g⁻¹ : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) i j ∈ O := by
  let τ : O →+* O := s.restrict O O hs
  have hτ : ∀ a : O, ((τ a : O) : T) = s a := fun a => rfl
  let JO : Matrix (Fin M) (Fin M) O := fun i j => ⟨JT i j, hJO i j⟩
  let x0 : Fin M → O := fun i => ⟨x i, hx i⟩
  let y0 : Fin M → O := fun i => ⟨y i, hy i⟩
  have hcoe : ∀ p q : Fin M → O, ((hform τ JO p q : O) : T) =
      hform s JT (fun i => (p i : T)) (fun i => (q i : T)) := by
    intro p q
    simp [hform, hτ, JO]
  have hβ0 : ((hform τ JO x0 x0 : O) : T) = hform s JT x x := hcoe x0 x0
  have hxy0 : hform τ JO x0 x0 = hform τ JO y0 y0 := Subtype.ext (by
    rw [hβ0, hxy]; exact (hcoe y0 y0).symm)
  have hunit : IsUnit (hform τ JO x0 x0) :=
    IsUnit.of_mul_eq_one ⟨w, hw⟩ (Subtype.ext (by
      rw [Subring.coe_mul, hβ0]; exact hxw))
  have hτinv : ∀ a : O, τ (τ a) = a := fun a => Subtype.ext (hss a)
  have hJ0 : ∀ i j, τ (JO j i) = JO i j := fun i j => Subtype.ext (hJ i j)
  have hfix : s (hform τ JO x0 x0 : O) = (hform τ JO x0 x0 : O) := by
    have := GlobalTheory.CompanionTheory.SW.QuasiRefl.hform_conj_symm hτinv hJ0 x0 x0
    exact congrArg Subtype.val this
  obtain ⟨ε, z, hε, hz⟩ := hgood (hform τ JO y0 x0) _ hunit hfix
  have hε' : ε * τ ε = 1 := Subtype.ext hε
  have hu : IsUnit (hform τ JO x0 x0 - τ ε * hform τ JO y0 x0) :=
    IsUnit.of_mul_eq_one z (Subtype.ext hz)
  obtain ⟨g0, hg0, hgx, -⟩ := GlobalTheory.CompanionTheory.SW.QuasiRefl.exists_unitary_carry O τ hτinv M JO hJ0 x0 y0 ε
    hxy0 hunit hε' hu
  have hval : ∀ g : GL (Fin M) O, ((bc O.subtype g : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) =
      (g : Matrix (Fin M) (Fin M) O).map O.subtype := fun g => rfl
  refine ⟨bc O.subtype g0, ?_, ?_, ?_, ?_⟩
  · have h0 : cT τ (g0 : Matrix (Fin M) (Fin M) O) * JO * (g0 : Matrix (Fin M) (Fin M) O) = JO := hg0
    have h1 := congrArg (RingHom.mapMatrix O.subtype) h0
    rw [map_mul, map_mul] at h1
    show cT s ((bc O.subtype g0 : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) * JT *
      ((bc O.subtype g0 : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) = JT
    have e1 : RingHom.mapMatrix O.subtype (cT τ (g0 : Matrix (Fin M) (Fin M) O)) =
        cT s ((bc O.subtype g0 : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) := by
      ext i j
      rfl
    have e2 : RingHom.mapMatrix O.subtype JO = JT := by
      ext i j
      rfl
    have e3 : RingHom.mapMatrix O.subtype (g0 : Matrix (Fin M) (Fin M) O) =
        ((bc O.subtype g0 : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) := rfl
    rwa [e1, e2, e3] at h1
  · funext i
    have := congrArg Subtype.val (congrFun hgx i)
    simpa [Matrix.mulVec, dotProduct, hval, x0, y0] using this
  · intro i j
    rw [hval]
    exact ((g0 : Matrix (Fin M) (Fin M) O) i j).2
  · intro i j
    rw [← map_inv, hval]
    exact (((g0⁻¹ : GL (Fin M) O) : Matrix (Fin M) (Fin M) O) i j).2

theorem mem_latV_iff {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d n M : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) (X : Fin n → Fin M → Fv F v ⊗[F] E) :
    X ∈ latV b v ↔ ∀ a i, X a i ∈ O :=
  ⟨fun h a i => (hO _).2 (h a i), fun h a i => (hO _).1 (h a i)⟩

theorem mulVec_mem {T : Type} [CommRing T] (O : Subring T) {M : ℕ} (g : Matrix (Fin M) (Fin M) T)
    (hg : ∀ i j, g i j ∈ O) (x : Fin M → T) (hx : ∀ i, x i ∈ O) (i : Fin M) : (g *ᵥ x) i ∈ O := by
  simp only [Matrix.mulVec, dotProduct]
  exact O.sum_mem fun j _ => O.mul_mem (hg i j) (hx j)

theorem good_trans : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ x y : Fin 1 → Fin M → Fv F v ⊗[F] E, x ∈ latV b v → y ∈ latV b v → gramR (Fv F v) σ J x = (hermScal (Fv F v) σ (algebraMap F _ t) : HermR (Fv F v) σ 1) → gramR (Fv F v) σ J y = gramR (Fv F v) σ J x → ∃ h : HA (Fv F v) σ J, actW (Fv F v) σ J h x = y ∧ ∀ (n : ℕ) (X : Fin n → Fin M → Fv F v ⊗[F] E), actW (Fv F v) σ J h X ∈ latV b v ↔ X ∈ latV b v := by
  intro F E _ _ _ _ _ σ h M J hJ t ht d b
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have I := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ h d b
  filter_upwards [GlobalTheory.CompanionTheory.SW.GoodRing.good_ring F E σ h d b, I.2 t ht,
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => I.1 (J i j)] with v hring hv hJv
  obtain ⟨O, hO, hstab, -, -, -, hgood, -⟩ := hring
  intro x y hx hy hxt hyx
  have hss : ∀ z : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      show a ⊗ₜ[F] σ (σ e) = a ⊗ₜ[F] e
      rw [hinv]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]
  have hc : ∀ c : Fv F v, c ∈ v.adicCompletionIntegers F → c ⊗ₜ[F] (1 : E) ∈ O := by
    intro c hcv
    refine (hO _).2 fun k => ?_
    have e : c ⊗ₜ[F] (1 : E) = c • (1 : Fv F v ⊗[F] E) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem hcv ((hO 1).1 O.one_mem k)
  set c : Fv F v := algebraMap F (Fv F v) t with hcdef
  have hc0 : c ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  have hβ : hform (sigR (Fv F v) σ) (JR (Fv F v) J) (x 0) (x 0) = c ⊗ₜ[F] (1 : E) :=
    congrFun (congrFun hxt 0) 0
  have hxy : hform (sigR (Fv F v) σ) (JR (Fv F v) J) (x 0) (x 0) =
      hform (sigR (Fv F v) σ) (JR (Fv F v) J) (y 0) (y 0) :=
    (congrFun (congrFun hyx 0) 0).symm
  have hci : c⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
  have hmul : c ⊗ₜ[F] (1 : E) * c⁻¹ ⊗ₜ[F] (1 : E) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hc0, mul_one,
      Algebra.TensorProduct.one_def]
  obtain ⟨g, hg, hgx, hgO, hgiO⟩ := transit_ring O (sigR (Fv F v) σ) hstab hss (JR (Fv F v) J)
    (fun i j => (hO _).2 (hJv i j))
    (fun i j => by
      show sigR (Fv F v) σ (inclR (Fv F v) (J j i)) = inclR (Fv F v) (J i j)
      rw [← hJ.1 i j]
      rfl)
    (x 0) (y 0) (fun i => (hO _).2 (hx 0 i)) (fun i => (hO _).2 (hy 0 i)) hxy
    (c⁻¹ ⊗ₜ[F] (1 : E)) (hc _ hci) (by rw [hβ, hmul]) hgood
  let h' : HA (Fv F v) σ J := (⟨g, hg⟩ : HR (Fv F v) σ J)
  have hact : ∀ {n : ℕ} (X : Fin n → Fin M → Fv F v ⊗[F] E) (a : Fin n),
      actW (Fv F v) σ J h' X a = (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ X a :=
    fun _ _ => rfl
  refine ⟨h', ?_, fun n X => ?_⟩
  · funext a
    rw [hact, Fin.fin_one_eq_zero a, hgx]
  · rw [mem_latV_iff b v O hO, mem_latV_iff b v O hO]
    constructor
    · intro hX a i
      have e : X a = ((g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ
          ((g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ X a) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rw [e]
      exact mulVec_mem O _ hgiO _ (fun j => by rw [← hact]; exact hX a j) i
    · intro hX a i
      rw [hact]
      exact mulVec_mem O _ hgO _ (hX a) i

end GlobalTheory.CompanionTheory.SW.GoodTrans
end

