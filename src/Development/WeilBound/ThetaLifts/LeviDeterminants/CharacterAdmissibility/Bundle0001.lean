module

public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0001
public import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.ResAdm

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.DoublingGramFromBlocks
section
noncomputable section

namespace PositivityTheory.ThKF0.Chr

open Matrix GlobalTheory.WeilM PositivityTheory.ThK.SiegelT

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {β β₁ μ ν : Type} [Fintype β] [DecidableEq β] [Fintype β₁] [DecidableEq β₁] [Fintype μ] [DecidableEq μ]
  [Fintype ν] [DecidableEq ν]


variable (c) in
structure Fr (J : Matrix β β E) (J₁ : Matrix β₁ β₁ E) (H : Matrix μ μ E) (ι : Matrix β β₁ E) (Z : Matrix β μ E)
    (π : Matrix β₁ β E) (ρ : Matrix μ β E) : Prop where
  one : ι * π + Z * ρ = 1
  pi : π * ι = 1
  pz : π * Z = 0
  ri : ρ * ι = 0
  rz : ρ * Z = 1
  gii : ιᵀ * J * ι.map c = J₁
  giz : ιᵀ * J * Z.map c = 0
  gzi : Zᵀ * J * ι.map c = 0
  gzz : Zᵀ * J * Z.map c = H

abbrev dd2 {a b : Type} (A : Matrix a b E) : Matrix (a ⊕ a) (b ⊕ b) E := fromBlocks A 0 0 A

variable {J : Matrix β β E} {J₁ : Matrix β₁ β₁ E} {H : Matrix μ μ E} {ι : Matrix β β₁ E} {Z : Matrix β μ E}
  {π : Matrix β₁ β E} {ρ : Matrix μ β E}

theorem doubling_gram_fromBlocks {a b : Type} (A : Matrix β a E) (B : Matrix β b E) :
    (dd2 A)ᵀ * dbl J * (dd2 B).map c = fromBlocks (Aᵀ * J * B.map c) 0 0 (-(Aᵀ * J * B.map c)) := by
  simp only [dbl, fromBlocks_transpose, fromBlocks_map, Matrix.map_zero _ (map_zero c), fromBlocks_multiply]
  simp

theorem Fr.dbl (h : Fr c J J₁ H ι Z π ρ) : Fr c (dbl J) (dbl J₁) (dbl H) (dd2 ι) (dd2 Z) (dd2 π) (dd2 ρ) := by
  exact
    { one := by simp [fromBlocks_multiply, fromBlocks_add, h.one]
      pi := by simp [fromBlocks_multiply, h.pi]
      pz := by simp [fromBlocks_multiply, h.pz]
      ri := by simp [fromBlocks_multiply, h.ri]
      rz := by simp [fromBlocks_multiply, h.rz]
      gii := by rw [doubling_gram_fromBlocks, h.gii]; rfl
      giz := by rw [doubling_gram_fromBlocks, h.giz]; simp
      gzi := by rw [doubling_gram_fromBlocks, h.gzi]; simp
      gzz := by rw [doubling_gram_fromBlocks, h.gzz]; rfl }

theorem Fr.mul (h : Fr c J J₁ H ι Z π ρ) (g g' : Matrix β₁ β₁ E) (k k' : Matrix μ μ E) :
    (ι * g * π + Z * k * ρ) * (ι * g' * π + Z * k' * ρ) = ι * (g * g') * π + Z * (k * k') * ρ := by
  have e : ∀ {a b a' b' : Type} [Fintype a] [Fintype b] [Fintype a'] [Fintype b'] (A : Matrix β a E) (x : Matrix a b E)
      (B : Matrix b β E) (A' : Matrix β a' E) (x' : Matrix a' b' E) (B' : Matrix b' β E),
      A * x * B * (A' * x' * B') = A * x * (B * A') * x' * B' := fun A x B A' x' B' => by simp only [Matrix.mul_assoc]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e, e, e, e, h.pi, h.pz, h.ri, h.rz]
  simp [Matrix.mul_assoc]

theorem Fr.gram (h : Fr c J J₁ H ι Z π ρ) (g : Matrix β₁ β₁ E) (k : Matrix μ μ E) :
    (ι * g * π + Z * k * ρ)ᵀ * J * (ι * g * π + Z * k * ρ).map c =
      πᵀ * (gᵀ * J₁ * g.map c) * π.map c + ρᵀ * (kᵀ * H * k.map c) * ρ.map c := by
  have e : ∀ {a a' : Type} [Fintype a] [Fintype a'] (A : Matrix β a E) (x : Matrix a a E)
      (B : Matrix a β E) (A' : Matrix β a' E) (x' : Matrix a' a' E) (B' : Matrix a' β E),
      (A * x * B)ᵀ * J * (A' * x' * B').map c = Bᵀ * (xᵀ * (Aᵀ * J * A'.map c) * x'.map c) * B'.map c :=
    fun A x B A' x' B' => by simp only [transpose_mul, map_mul', Matrix.mul_assoc]
  rw [Matrix.map_add _ (map_add c), transpose_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e, e, e, e,
    h.gii, h.giz, h.gzi, h.gzz]
  simp

def Fr.emb (h : Fr c J J₁ H ι Z π ρ) : UG c J₁ × UG c H →* UG c J where
  toFun p := ⟨⟨ι * p.1.1.1 * π + Z * p.2.1.1 * ρ, ι * (p.1.1⁻¹).1 * π + Z * (p.2.1⁻¹).1 * ρ,
    by rw [h.mul, Units.mul_inv, Units.mul_inv, Matrix.mul_one, Matrix.mul_one, h.one],
    by rw [h.mul, Units.inv_mul, Units.inv_mul, Matrix.mul_one, Matrix.mul_one, h.one]⟩, by
      have e := h.gram 1 1
      rw [Matrix.mul_one, Matrix.mul_one, h.one, transpose_one, transpose_one, transpose_one, map_one', map_one', map_one',
        Matrix.mul_one, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul, Matrix.one_mul] at e
      refine (h.gram _ _).trans (Eq.trans ?_ e.symm)
      rw [show p.1.1.1ᵀ * J₁ * p.1.1.1.map c = J₁ from p.1.2, show p.2.1.1ᵀ * H * p.2.1.1.map c = H from p.2.2]⟩
  map_one' := Subtype.ext (Units.ext (by
    show ι * 1 * π + Z * 1 * ρ = 1
    rw [Matrix.mul_one, Matrix.mul_one, h.one]))
  map_mul' p q := Subtype.ext (Units.ext (h.mul _ _ _ _).symm)

theorem Fr.emb_i (h : Fr c J J₁ H ι Z π ρ) (p : UG c J₁ × UG c H) : (h.emb p).1.1 * ι = ι * p.1.1.1 := by
  show (ι * p.1.1.1 * π + Z * p.2.1.1 * ρ) * ι = _
  rw [Matrix.add_mul, Matrix.mul_assoc, h.pi, Matrix.mul_assoc (Z * _), h.ri]
  simp

theorem Fr.embeddingAtLocalFactor (h : Fr c J J₁ H ι Z π ρ) (p : UG c J₁ × UG c H) : (h.emb p).1.1 * Z = Z * p.2.1.1 := by
  show (ι * p.1.1.1 * π + Z * p.2.1.1 * ρ) * Z = _
  rw [Matrix.add_mul, Matrix.mul_assoc, h.pz, Matrix.mul_assoc (Z * _), h.rz]
  simp

theorem Fr.continuous_emb [TopologicalSpace E] [IsTopologicalRing E] (h : Fr c J J₁ H ι Z π ρ) :
    Continuous fun g : UG c J₁ => h.emb (g, 1) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact ((continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul
      continuous_const).add (continuous_const (y := Z * (1 : Matrix μ μ E) * ρ))
  · exact ((continuous_const.matrix_mul (Units.continuous_coe_inv.comp continuous_subtype_val)).matrix_mul
      continuous_const).add (continuous_const (y := Z * (1 : Matrix μ μ E) * ρ))

abbrev hyp (ν : Type) [DecidableEq ν] (η : ℤˣ) : Matrix (ν ⊕ ν) (ν ⊕ ν) E := fromBlocks 0 1 (((η : ℤ) : E) • 1) 0

theorem eta_sq (η : ℤˣ) : ((η : ℤ) : E) * ((η : ℤ) : E) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp

theorem exists_gamma0 (η : ℤˣ) : ∃ γ : UG c (dbl (hyp ν η : Matrix _ _ E)), γ.1.1 * (diagCols (ν ⊕ ν) : Matrix _ _ E) =
    dd2 (fromRows (1 : Matrix ν ν E) (0 : Matrix ν ν E)) * (fromBlocks 1 0 0 (((η : ℤ) : E) • 1) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) := by
  set a : E := ((η : ℤ) : E) with ha
  have h2 : a * a = 1 := eta_sq η
  have hca : (a • (1 : Matrix ν ν E)).map c = a • 1 := by
    ext i j; by_cases h : i = j <;> simp [h, ha, Matrix.one_apply]
  have hm1 : (-1 : Matrix ν ν E).map c = -1 := by rw [Matrix.map_neg _ (map_neg c), map_one']
  have hz : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
  let g : Matrix ((ν ⊕ ν) ⊕ (ν ⊕ ν)) ((ν ⊕ ν) ⊕ (ν ⊕ ν)) E :=
    fromBlocks (fromBlocks 1 0 0 1) (fromBlocks 0 0 0 (-1)) (fromBlocks 0 0 (-1) 0) (fromBlocks 0 (a • 1) 1 0)
  let g' : Matrix ((ν ⊕ ν) ⊕ (ν ⊕ ν)) ((ν ⊕ ν) ⊕ (ν ⊕ ν)) E :=
    fromBlocks (fromBlocks 1 0 0 1) (fromBlocks 0 0 (a • 1) 0) (fromBlocks 1 0 0 0) (fromBlocks 0 1 (a • 1) 0)
  refine ⟨⟨⟨g, g', ?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [g, g', fromBlocks_multiply, fromBlocks_add, ← fromBlocks_one, ← fromBlocks_zero]
    simp [smul_smul, h2]
  · simp only [g, g', fromBlocks_multiply, fromBlocks_add, ← fromBlocks_one, ← fromBlocks_zero]
    simp [smul_smul, h2]
  · show gᵀ * _ * g.map c = _
    simp only [g, hyp, ← ha, dbl, fromBlocks_transpose, fromBlocks_map, map_one', hm1, hz, hca, fromBlocks_neg, ← fromBlocks_zero,
      fromBlocks_multiply, fromBlocks_add]
    simp [smul_smul, h2]
  · show g * diagCols (E := E) (ν ⊕ ν) = _
    simp only [g, diagCols, fromBlocks_mul_fromRows, Matrix.mul_one, fromBlocks_add, fromBlocks_multiply]
    ext ((i | i) | (i | i)) (j | j) <;> simp

theorem Fr.exists_gamma {η : ℤˣ} {X Y : Matrix β ν E} {ρ : Matrix (ν ⊕ ν) β E}
    (h : Fr c J J₁ (hyp ν η) ι (fromCols X Y) π ρ) :
    ∃ (γ : UG c (GlobalTheory.WeilM.dbl J)) (s : Matrix (β₁ ⊕ (ν ⊕ ν)) β E) (s' : Matrix β (β₁ ⊕ (ν ⊕ ν)) E), s * s' = 1 ∧ s' * s = 1 ∧
      γ.1.1 * (diagCols β : Matrix _ _ E) = fromCols (dd2 ι * diagCols (E := E) β₁) (dd2 X) * s := by
  obtain ⟨γ₀, hγ⟩ := exists_gamma0 (c := c) (ν := ν) η
  set s₀ : Matrix (ν ⊕ ν) (ν ⊕ ν) E := fromBlocks 1 0 0 (((η : ℤ) : E) • 1)
  have hs : s₀ * s₀ = 1 := by simp [s₀, fromBlocks_multiply, smul_smul, eta_sq]
  set Z := fromCols X Y
  refine ⟨h.dbl.emb (1, γ₀), fromRows π (s₀ * ρ), fromCols ι (Z * s₀), ?_, ?_, ?_⟩
  · rw [fromRows_mul_fromCols, ← Matrix.mul_assoc π, Matrix.mul_assoc s₀, Matrix.mul_assoc s₀, ← Matrix.mul_assoc ρ,
      h.pi, h.pz, h.ri, h.rz, Matrix.one_mul, hs]
    simp
  · rw [fromCols_mul_fromRows, Matrix.mul_assoc, ← Matrix.mul_assoc s₀, hs, Matrix.one_mul, h.one]
  · have e : (diagCols β : Matrix _ _ E) = dd2 ι * (diagCols (E := E) β₁ * π) + dd2 Z * (diagCols (E := E) (ν ⊕ ν) * ρ) := by
      simp only [diagCols, fromRows_mul, fromBlocks_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]
      rw [← h.one]
      ext (i | i) j <;> rfl
    have e2 : dd2 Z * dd2 (fromRows (1 : Matrix ν ν E) (0 : Matrix ν ν E)) = dd2 X := by
      rw [fromBlocks_multiply]
      simp [Z, fromCols_mul_fromRows]
    rw [e, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc _ (dd2 Z), Fr.emb_i, Fr.embeddingAtLocalFactor, fromCols_mul_fromRows,
      Matrix.mul_assoc (dd2 Z), ← Matrix.mul_assoc γ₀.1.1, hγ, ← e2]
    simp only [Matrix.mul_assoc]
    simp

end PositivityTheory.ThKF0.Chr
end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.SchrodingerApplyZeroOfFst
section
noncomputable section

namespace PositivityTheory.ThKF0.Chr

open Matrix GlobalTheory.WeilM

variable {R : Type} [CommRing R] [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ}
  {κ κ₁ : Type} [Fintype κ] [Fintype κ₁]

theorem schrodinger_translate_apply (x : κ → R) (φ : (κ → R) → ℂ) : schr ψ (x, 0) φ = fun z => φ (z + x) := by
  funext z; simp [schr]

theorem schrodinger_apply_zero_of_fst {w : V R κ} (h : w.1 = 0) (φ : (κ → R) → ℂ) : schr ψ w φ 0 = φ 0 := by
  simp [schr, h]

theorem schr_zero (φ : (κ → R) → ℂ) : schr ψ (0 : V R κ) φ = φ := by
  funext z; simp [schr]

theorem schr_add {w w' : V R κ} (h : w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = schr ψ (w + w') φ := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self _
  linear_combination (⅟(2 : R)) * h - (w.1 ⬝ᵥ w'.2) * h2

omit [Invertible (2 : R)] in
theorem IsSp.symm {S : V R κ ≃ₗ[R] V R κ} (h : IsSp S) : IsSp S.symm := fun w w' => by
  have := h (S.symm w) (S.symm w')
  simpa using this.symm

omit [Invertible (2 : R)] in
theorem IsSp.trans {S S' : V R κ ≃ₗ[R] V R κ} (h : IsSp S) (h' : IsSp S') : IsSp (S.trans S') := fun w w' =>
  (h' (S w) (S w')).trans (h w w')

structure IsImp (C : TestClass R) (ψ : AddChar R ℂ) (S : V R κ ≃ₗ[R] V R κ) (T : Module.End ℂ ((κ → R) → ℂ)) : Prop where
  maps : ∀ φ ∈ C.sp κ, T φ ∈ C.sp κ
  adm : ∀ l ∈ C.adm κ, l ∘ₗ T ∈ C.adm κ
  law : ∀ w, ∀ φ ∈ C.sp κ, T (schr ψ w φ) = schr ψ (S w) (T φ)
  inj : ∀ φ ∈ C.sp κ, T φ = 0 → φ = 0

theorem AxImp.ex (h : AxImp C ψ) {S : V R κ ≃ₗ[R] V R κ} (hS : IsSp S) : ∃ T, IsImp C ψ S T := by
  obtain ⟨T, h1, h2, h3, h4⟩ := h κ S hS
  exact ⟨T, h1, h2, h3, h4⟩

structure Ax (C : TestClass R) (ψ : AddChar R ℂ) : Prop extends AxB C ψ where
  delta : AxDelta C ψ
  imp : AxImp C ψ

def Cyc (C : TestClass R) (ψ : AddChar R ℂ) (l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ φ ∈ C.sp κ, φ ≠ 0 → ∃ w, l (schr ψ w φ) ≠ 0

theorem Cyc.ne (h : Ax C ψ) {l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ} (hl : Cyc C ψ l) : ∃ φ ∈ C.sp κ, l φ ≠ 0 := by
  obtain ⟨φ, hφ, h0⟩ := h.ne κ
  obtain ⟨w, hw⟩ := hl φ hφ h0
  exact ⟨_, h.schr κ w φ hφ, hw⟩

theorem Ax.schur (h : Ax C ψ) (T : Module.End ℂ ((κ → R) → ℂ)) (ha : Chr.ev0 R κ ∘ₗ T ∈ C.adm κ)
    (hc : ∀ w, ∀ φ ∈ C.sp κ, T (schr ψ w φ) = schr ψ w (T φ)) : ∃ a : ℂ, ∀ φ ∈ C.sp κ, T φ = a • φ := by
  obtain ⟨a, ha⟩ := h.delta κ _ ha fun y φ hφ => by
    show T _ 0 = T φ 0
    rw [hc _ _ hφ, schrodinger_apply_zero_of_fst rfl]
  refine ⟨a, fun φ hφ => funext fun x => ?_⟩
  have e : T (schr ψ (x, 0) φ) 0 = a * schr ψ (x, 0) φ 0 := ha _ (h.schr κ _ φ hφ)
  rw [hc _ _ hφ, schrodinger_translate_apply, schrodinger_translate_apply] at e
  simpa using e

theorem Ax.line (h : Ax C ψ) {S : V R κ ≃ₗ[R] V R κ} (hS : IsSp S) {T : Module.End ℂ ((κ → R) → ℂ)} (hT : IsImp C ψ S T)
    {l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ C.adm κ) (hinv : ∀ w, (S w).1 = 0 → ∀ φ ∈ C.sp κ, l (schr ψ w φ) = l φ) :
    ∃ a : ℂ, ∀ φ ∈ C.sp κ, l φ = a * T φ 0 := by
  obtain ⟨T', hT'⟩ := h.imp.ex hS.symm
  obtain ⟨a, ha⟩ := h.delta κ _ (hT'.adm l hl) fun y φ hφ => by
    show l (T' _) = l (T' φ)
    rw [hT'.law _ _ hφ, hinv _ (by simp) _ (hT'.maps φ hφ)]
  obtain ⟨b, hb⟩ := h.schur (T' ∘ₗ T) (hT.adm _ (hT'.adm _ (h.ev0 κ))) fun w φ hφ => by
    show T' (T _) = schr ψ w (T' (T φ))
    rw [hT.law _ _ hφ, hT'.law _ _ (hT.maps φ hφ), S.symm_apply_apply]
  have hb0 : b ≠ 0 := fun e => by
    obtain ⟨φ, hφ, h0⟩ := h.ne κ
    have := hb φ hφ
    rw [e, zero_smul] at this
    exact h0 (hT.inj φ hφ (hT'.inj _ (hT.maps φ hφ) this))
  refine ⟨b⁻¹ * a, fun φ hφ => ?_⟩
  have e : l (T' (T φ)) = a * T φ 0 := ha _ (hT.maps φ hφ)
  rw [show T' (T φ) = b • φ from hb φ hφ, map_smul, smul_eq_mul] at e
  rw [mul_assoc, ← e, inv_mul_cancel_left₀ hb0]

theorem IsImp.cyc {S : V R κ ≃ₗ[R] V R κ} {T : Module.End ℂ ((κ → R) → ℂ)} (hT : IsImp C ψ S T) {φ : (κ → R) → ℂ}
    (hφ : φ ∈ C.sp κ) (h0 : φ ≠ 0) : ∃ w, T (schr ψ w φ) 0 ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 fun e => h0 (hT.inj φ hφ e)
  refine ⟨S.symm (x, 0), ?_⟩
  rw [hT.law _ _ hφ, S.apply_symm_apply, schrodinger_translate_apply]
  simpa using hx

theorem Ax.cyc (h : Ax C ψ) {S : V R κ ≃ₗ[R] V R κ} (hS : IsSp S)
    {l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ C.adm κ) (hinv : ∀ w, (S w).1 = 0 → ∀ φ ∈ C.sp κ, l (schr ψ w φ) = l φ)
    (hne : ∃ φ ∈ C.sp κ, l φ ≠ 0) : Cyc C ψ l := by
  obtain ⟨T, hT⟩ := h.imp.ex hS
  obtain ⟨a, ha⟩ := h.line hS hT hl hinv
  obtain ⟨φ₀, h₀, hne⟩ := hne
  have ha0 : a ≠ 0 := fun e => hne (by rw [ha _ h₀, e, zero_mul])
  intro φ hφ h0
  obtain ⟨w, hw⟩ := hT.cyc hφ h0
  exact ⟨w, by rw [ha _ (h.schr κ w φ hφ)]; exact mul_ne_zero ha0 hw⟩

theorem Ax.exists_form (h : Ax C ψ) {S : V R κ ≃ₗ[R] V R κ} (hS : IsSp S) : ∃ l ∈ C.adm κ,
    (∀ w, (S w).1 = 0 → ∀ φ ∈ C.sp κ, l (schr ψ w φ) = l φ) ∧ Cyc C ψ l := by
  obtain ⟨T, hT⟩ := h.imp.ex hS
  refine ⟨_, hT.adm _ (h.ev0 κ), fun w hw φ hφ => ?_, fun φ hφ h0 => hT.cyc hφ h0⟩
  show T _ 0 = T φ 0
  rw [hT.law _ _ hφ, schrodinger_apply_zero_of_fst hw]

def Law (C : TestClass R) (ψ : AddChar R ℂ) (S : V R κ ≃ₗ[R] V R κ) (j : κ₁ → κ)
    (e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) : Prop :=
  ∀ w w₁, Rel S j w w₁ → ∀ φ ∈ C.sp κ, e (schr ψ w φ) = schr ψ w₁ (e φ)

structure IsE (C : TestClass R) (ψ : AddChar R ℂ) (S : V R κ ≃ₗ[R] V R κ) (j : κ₁ → κ)
    (e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) : Prop where
  maps : ∀ φ ∈ C.sp κ, e φ ∈ C.sp κ₁
  adm : ∀ l ∈ C.adm κ₁, l ∘ₗ e ∈ C.adm κ
  law : Law C ψ S j e
  ne : ∃ φ ∈ C.sp κ, e φ ≠ 0

omit [Invertible (2 : R)] in
theorem extend_dot {j : κ₁ → κ} (hj : Function.Injective j) (a : κ₁ → R) (y : κ → R) :
    Function.extend j a 0 ⬝ᵥ y = a ⬝ᵥ (y ∘ j) := by
  classical
  refine (Fintype.sum_of_injective j hj _ _ (fun k hk => ?_) fun i => ?_).symm
  · rw [Function.extend_apply' _ _ _ hk]; simp
  · rw [hj.extend_apply]; rfl

omit [Invertible (2 : R)] [Fintype κ] [Fintype κ₁] in
theorem extend_add {j : κ₁ → κ} (hj : Function.Injective j) (a b : κ₁ → R) :
    Function.extend j (a + b) 0 = Function.extend j a 0 + Function.extend j b 0 := by
  funext k
  by_cases h : ∃ x, j x = k
  · obtain ⟨x, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

omit [Invertible (2 : R)] [Fintype κ] [Fintype κ₁] in
theorem extend_zero' {j : κ₁ → κ} (hj : Function.Injective j) : Function.extend j (0 : κ₁ → R) 0 = 0 := by
  funext k
  by_cases h : ∃ x, j x = k
  · obtain ⟨x, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

omit [Invertible (2 : R)] [Fintype κ] [Fintype κ₁] in
theorem rel_lift {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} (hj : Function.Injective j) (w₁ : V R κ₁) :
    Rel S j (S.symm (Function.extend j w₁.1 0, Function.extend j w₁.2 0)) w₁ := by
  rw [Rel, S.apply_symm_apply]
  exact ⟨rfl, Function.extend_comp hj _ _⟩

theorem IsImp.law_res {S : V R κ ≃ₗ[R] V R κ} {T : Module.End ℂ ((κ → R) → ℂ)} (hT : IsImp C ψ S T) {j : κ₁ → κ}
    (hj : Function.Injective j) : Law C ψ S j (res R j ∘ₗ T) := fun w w₁ hw φ hφ => by
  funext x
  show T _ (Function.extend j x 0) = schr ψ w₁ (fun y => T φ (Function.extend j y 0)) x
  rw [hT.law _ _ hφ]
  simp only [schr, hw.1, extend_dot hj, hw.2, extend_add hj]

theorem Ax.isE_res (h : Ax C ψ) {S : V R κ ≃ₗ[R] V R κ} {T : Module.End ℂ ((κ → R) → ℂ)} (hT : IsImp C ψ S T) {j : κ₁ → κ}
    (hj : Function.Injective j) : IsE C ψ S j (res R j ∘ₗ T) := by
  refine ⟨fun φ hφ => h.res _ _ j hj _ (hT.maps φ hφ), fun l hl => hT.adm _ (h.res_adm _ _ j hj l hl), hT.law_res hj, ?_⟩
  obtain ⟨φ, hφ, h0⟩ := h.ne κ
  obtain ⟨w, hw⟩ := hT.cyc hφ h0
  refine ⟨_, h.schr κ w φ hφ, fun e => hw ?_⟩
  have := congrFun e 0
  rwa [LinearMap.comp_apply, res, LinearMap.funLeft_apply, extend_zero' hj] at this

theorem Ax.exists_E (h : Ax C ψ) {S : V R κ ≃ₗ[R] V R κ} (hS : IsSp S) {j : κ₁ → κ} (hj : Function.Injective j) :
    ∃ e, IsE C ψ S j e := by
  obtain ⟨T, hT⟩ := h.imp.ex hS
  exact ⟨_, h.isE_res hT hj⟩

variable {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e e' : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}

theorem Law.inv (he : Law C ψ S j e) (hj : Function.Injective j) (w : V R κ) (hw : (S w).1 = 0) (φ : (κ → R) → ℂ)
    (hφ : φ ∈ C.sp κ) : (ev0 R κ₁ ∘ₗ e) (schr ψ w φ) = (ev0 R κ₁ ∘ₗ e) φ := by
  show e _ 0 = e φ 0
  rw [he w (0, (S w).2 ∘ j) ⟨by rw [hw, extend_zero' hj], rfl⟩ φ hφ, schrodinger_apply_zero_of_fst rfl]

theorem Law.apply (he : Law C ψ S j e) (hj : Function.Injective j) (y : κ₁ → R) : ∃ w, ∀ e', Law C ψ S j e' →
    ∀ φ ∈ C.sp κ, e' φ y = e' (schr ψ w φ) 0 :=
  ⟨_, fun e' he' φ hφ => by rw [he' _ (y, 0) (rel_lift hj _) φ hφ, schrodinger_translate_apply]; simp⟩

theorem Ax.E_cyc (h : Ax C ψ) (hS : IsSp S) (hj : Function.Injective j) (he : IsE C ψ S j e) :
    Cyc C ψ (Chr.ev0 R κ₁ ∘ₗ e) := by
  refine h.cyc hS (he.adm _ (h.ev0 _)) (he.law.inv hj) ?_
  obtain ⟨φ, hφ, h0⟩ := he.ne
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h0
  obtain ⟨w, hw⟩ := he.law.apply hj y
  exact ⟨_, h.schr κ w φ hφ, fun e0 => hy ((hw e he.law φ hφ).trans e0)⟩

theorem Ax.comp_cyc (h : Ax C ψ) (hS : IsSp S) (hj : Function.Injective j) (he : IsE C ψ S j e)
    {l : ((κ₁ → R) → ℂ) →ₗ[ℂ] ℂ} (hl : Cyc C ψ l) : ∀ φ ∈ C.sp κ, φ ≠ 0 → ∃ w w', l (e (schr ψ w' (schr ψ w φ))) ≠ 0 := by
  intro φ hφ h0
  obtain ⟨w, hw⟩ := h.E_cyc hS hj he φ hφ h0
  have hs := h.schr κ w φ hφ
  obtain ⟨w₁, hw₁⟩ := hl _ (he.maps _ hs) fun e0 => hw (congrFun e0 0)
  exact ⟨w, _, by rwa [he.law _ w₁ (rel_lift hj _) _ hs]⟩

theorem Ax.comp_ne (h : Ax C ψ) (hS : IsSp S) (hj : Function.Injective j) (he : IsE C ψ S j e)
    {l : ((κ₁ → R) → ℂ) →ₗ[ℂ] ℂ} (hl : Cyc C ψ l) : ∃ φ ∈ C.sp κ, l (e φ) ≠ 0 := by
  obtain ⟨φ, hφ, h0⟩ := h.ne κ
  obtain ⟨w, w', hw⟩ := h.comp_cyc hS hj he hl φ hφ h0
  exact ⟨_, h.schr _ _ _ (h.schr _ _ _ hφ), hw⟩

theorem Ax.uniq (h : Ax C ψ) (hS : IsSp S) (hj : Function.Injective j) (he : IsE C ψ S j e) (he' : Law C ψ S j e')
    (ha : Chr.ev0 R κ₁ ∘ₗ e' ∈ C.adm κ) : ∃ c : ℂ, ∀ φ ∈ C.sp κ, e' φ = c • e φ := by
  obtain ⟨T, hT⟩ := h.imp.ex hS
  obtain ⟨a, ha⟩ := h.line hS hT ha (he'.inv hj)
  obtain ⟨b, hb⟩ := h.line hS hT (he.adm _ (h.ev0 _)) (he.law.inv hj)
  obtain ⟨φ₀, h₀, hne⟩ := (h.E_cyc hS hj he).ne h
  have hb0 : b ≠ 0 := fun e => hne (by rw [hb _ h₀, e, zero_mul])
  refine ⟨a / b, fun φ hφ => funext fun y => ?_⟩
  obtain ⟨w, hw⟩ := he'.apply hj y
  have hs := h.schr κ w φ hφ
  rw [Pi.smul_apply, hw e' he' φ hφ, hw e he.law φ hφ, show e' _ 0 = _ from ha _ hs, show e _ 0 = _ from hb _ hs, smul_eq_mul]
  field_simp

end PositivityTheory.ThKF0.Chr
end
end

