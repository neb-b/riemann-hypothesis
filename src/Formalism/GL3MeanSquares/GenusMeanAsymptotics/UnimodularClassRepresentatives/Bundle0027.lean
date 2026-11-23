module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0023
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0025
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0015
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0013
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0020
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0007
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsFracOfFixed

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormSpanEqProd
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem BrA.normD_eq_tprod (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) :
    normD h L = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ vd h L 𝔭.1 := by
  have hD := LocF.discrIdeal_ne_bot (LocF.aniso_of_totPosDef hd) hL hLi
  have hD' : BrA.discrF F h L ≠ ⊥ := by
    intro e
    apply hD
    rw [BrA.discrIdeal_eq_map hF hs, e, Ideal.map_bot]
  rw [BrA.normD_eq hK hF hs, BrA.absNorm_eq_tprod hD']
  exact tprod_congr fun 𝔭 => by rw [BrA.vd_eq hF hs]

theorem integral_of_mem_genus (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {M : Submodule (𝓞 K) V} (hM : M ∈ Formalism.HermitianLatticesTheory.genus h L) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h M ∧ (∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → vd h M 𝔭 = vd h L 𝔭) ∧
      normD h M = normD h L := by
  obtain ⟨hMl, hMg⟩ := hM
  have key : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = locF 𝔭 M := by
    intro 𝔭 h𝔭
    obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
    rw [locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
    exact hMg P hP
  have hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h M := by
    intro x hx y hy
    rw [← LocF.iInf_locF (F := F) (1 : Submodule (𝓞 K) K), Submodule.mem_iInf]
    intro 𝔭
    obtain ⟨g, hg, e⟩ := key 𝔭.1 𝔭.2
    exact BrA.form_mem_locF hF hLi 𝔭.2.isPrime hg (e ▸ LocF.le_locF 𝔭.1 M hx)
      (e ▸ LocF.le_locF 𝔭.1 M hy)
  have hvd : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → vd h M 𝔭 = vd h L 𝔭 := by
    intro 𝔭 h𝔭
    obtain ⟨g, hg, e⟩ := key 𝔭 h𝔭
    rw [← localizedQuotients.vd_locF hF h M h𝔭, ← localizedQuotients.vd_locF hF h L h𝔭, ← e]
    unfold vd
    rw [BrA.discrIdeal_gmap hg]
  refine ⟨hMi, hvd, ?_⟩
  rw [BrA.normD_eq_tprod hK hF hs hd hMl hMi, BrA.normD_eq_tprod hK hF hs hd hL hLi]
  exact tprod_congr fun 𝔭 => by rw [hvd 𝔭.1 𝔭.2]

theorem normD_eq_prod (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) :
    normD h L = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ vd h L 𝔭.1 :=
  BrA.normD_eq_tprod hK hF hs hd hL hLi

theorem absNorm_span_eq_prod (n : 𝓞 F) (hn : n ≠ 0) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ vF 𝔭.1 n := by
  have hI : Ideal.span {n} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [BrA.absNorm_eq_tprod hI]
  refine tprod_congr fun 𝔭 => ?_
  unfold vF
  simp only [Ideal.span_singleton_le_iff_mem]

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.BoxInterEqEmpty
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem sum_ballCount_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {s : Finset (Submodule (𝓞 K) V)} (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s)
    {T : ℝ} (hT : 0 ≤ T) :
    ∑ M ∈ s, (ballCount h M T : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ) =
      Formalism.HermitianLatticesTheory.mass h L + ∑ᶠ n ∈ boxSet K F T, repMass h L (algebraMap F K (n : F)) := by
  exact BallSum.sum_ballCount hK hF hs hd hL hLi hsr hT

theorem box_inter_eq_empty (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)}
    {T : ℝ} (hbT : T ^ Formalism.HermitianLatticesTheory.fDeg K < (Ideal.absNorm b : ℝ)) :
    {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ b} = ∅ := by
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hn hb
  have := BoxCube.absNorm_le_pow hK hF hn hb
  linarith

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.EqBlockOfFix
section
open Matrix

namespace Formalism.HermitianLattices.Ext.L3.PinE

variable {A : Type*} [CommRing A] [StarRing A] {κ : Type} [Fintype κ] [DecidableEq κ]

def e₀ : Unit ⊕ κ → A := Pi.single (Sum.inl ()) 1

def HH (H' : Matrix κ κ A) : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A := fromBlocks 1 0 0 H'

theorem form_block (H' X' : Matrix κ κ A) :
    (fromBlocks 1 0 0 X' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A)ᴴ * HH H' * fromBlocks 1 0 0 X' =
      fromBlocks 1 0 0 (X'ᴴ * H' * X') := by
  simp [HH, fromBlocks_conjTranspose, fromBlocks_multiply]

theorem block_mulVec_e₀ (X' : Matrix κ κ A) :
    (fromBlocks 1 0 0 X' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A) *ᵥ e₀ = e₀ := by
  unfold e₀
  rw [mulVec_single_one]
  ext i
  rcases i with ⟨⟩ | i <;> simp

theorem eq_block_of_fix {H' : Matrix κ κ A} {Y : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A}
    (hY : Yᴴ * HH H' * Y = HH H') (h0 : Y *ᵥ e₀ = e₀) :
    Y.toBlocks₂₂ᴴ * H' * Y.toBlocks₂₂ = H' ∧ Y = fromBlocks 1 0 0 Y.toBlocks₂₂ := by
  have h11 : Y (Sum.inl ()) (Sum.inl ()) = 1 := by
    have := congrFun h0 (Sum.inl ())
    simpa [e₀, mulVec_single_one] using this
  have h21 : ∀ i, Y (Sum.inr i) (Sum.inl ()) = 0 := by
    intro i
    have := congrFun h0 (Sum.inr i)
    simpa [e₀, mulVec_single_one] using this
  have hA : Y.toBlocks₁₁ = 1 := by
    ext ⟨⟩ ⟨⟩
    simpa [toBlocks₁₁] using h11
  have hC : Y.toBlocks₂₁ = 0 := by
    ext i ⟨⟩
    simpa [toBlocks₂₁] using h21 i
  have hYb : Y = fromBlocks 1 Y.toBlocks₁₂ 0 Y.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks Y]
    rw [hA, hC]
  rw [hYb] at hY
  have key := congrArg Matrix.toBlocks₁₂ hY
  have key2 := congrArg Matrix.toBlocks₂₂ hY
  simp [HH, fromBlocks_conjTranspose, fromBlocks_multiply] at key key2
  refine ⟨?_, ?_⟩
  · simpa [key] using key2
  · rw [key] at hYb
    exact hYb

theorem form_col {H X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A} (hX : Xᴴ * H * X = H)
    (h00 : H (Sum.inl ()) (Sum.inl ()) = 1) : star (X *ᵥ e₀) ⬝ᵥ (H *ᵥ (X *ᵥ e₀)) = 1 := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hX]
  simp [e₀, mulVec_single_one, dotProduct, Fintype.sum_sum_type, h00]

theorem card_split [Finite A] (H' : Matrix κ κ A)
    (htr : ∀ x : Unit ⊕ κ → A, star x ⬝ᵥ (HH H' *ᵥ x) = 1 →
      ∃ G G' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A, Gᴴ * HH H' * G = HH H' ∧ G * G' = 1 ∧ G *ᵥ e₀ = x) :
    Nat.card {X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A // Xᴴ * HH H' * X = HH H'} =
      Nat.card {x : Unit ⊕ κ → A // star x ⬝ᵥ (HH H' *ᵥ x) = 1} *
        Nat.card {X' : Matrix κ κ A // X'ᴴ * H' * X' = H'} := by
  classical
  choose G G' hG using htr
  have h00 : HH H' (Sum.inl ()) (Sum.inl ()) = (1 : A) := by simp [HH]
  have hinv : ∀ x hx, G' x hx * G x hx = 1 := fun x hx => by
    first
      | exact mul_eq_one_comm.mp (hG x hx).2.1
      | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) (hG x hx).2.1
      | exact (Matrix.mul_eq_one_comm (M := G x hx) (N := G' x hx)).mp (hG x hx).2.1
  have hG'form : ∀ x hx, (G' x hx)ᴴ * HH H' * G' x hx = HH H' := by
    intro x hx
    calc (G' x hx)ᴴ * HH H' * G' x hx = (G' x hx)ᴴ * ((G x hx)ᴴ * HH H' * G x hx) * G' x hx := by
          rw [(hG x hx).1]
      _ = (G x hx * G' x hx)ᴴ * HH H' * (G x hx * G' x hx) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = HH H' := by rw [(hG x hx).2.1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hGeq : ∀ x y (hx : star x ⬝ᵥ (HH H' *ᵥ x) = 1) (hy : star y ⬝ᵥ (HH H' *ᵥ y) = 1), x = y →
      G x hx = G y hy ∧ G' x hx = G' y hy := by
    rintro x _ hx hy rfl
    exact ⟨rfl, rfl⟩
  have fixY : ∀ (X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A) (hX : Xᴴ * HH H' * X = HH H'),
      (G' (X *ᵥ e₀) (form_col hX h00) * X)ᴴ * HH H' * (G' (X *ᵥ e₀) (form_col hX h00) * X) = HH H' ∧
      (G' (X *ᵥ e₀) (form_col hX h00) * X) *ᵥ e₀ = e₀ := by
    intro X hX
    constructor
    · calc _ = Xᴴ * ((G' (X *ᵥ e₀) (form_col hX h00))ᴴ * HH H' * G' (X *ᵥ e₀) (form_col hX h00)) * X := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = HH H' := by rw [hG'form, hX]
    · have h1 : G' (X *ᵥ e₀) (form_col hX h00) *ᵥ (G (X *ᵥ e₀) (form_col hX h00) *ᵥ e₀) = e₀ := by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      rw [(hG _ _).2.2] at h1
      rw [← Matrix.mulVec_mulVec]
      exact h1
  have recon : ∀ (X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A) (hX : Xᴴ * HH H' * X = HH H'),
      X = G (X *ᵥ e₀) (form_col hX h00) *
        fromBlocks 1 0 0 (G' (X *ᵥ e₀) (form_col hX h00) * X).toBlocks₂₂ := by
    intro X hX
    rw [← (eq_block_of_fix (fixY X hX).1 (fixY X hX).2).2, ← Matrix.mul_assoc, (hG _ _).2.1,
      Matrix.one_mul]
  let f : {X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A // Xᴴ * HH H' * X = HH H'} →
      {x : Unit ⊕ κ → A // star x ⬝ᵥ (HH H' *ᵥ x) = 1} × {X' : Matrix κ κ A // X'ᴴ * H' * X' = H'} :=
    fun X => (⟨X.1 *ᵥ e₀, form_col X.2 h00⟩,
      ⟨_, (eq_block_of_fix (fixY X.1 X.2).1 (fixY X.1 X.2).2).1⟩)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨X1, hX1⟩ ⟨X2, hX2⟩ h
      simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨hGG, hGG'⟩ := hGeq _ _ (form_col hX1 h00) (form_col hX2 h00) h1
      apply Subtype.ext
      dsimp only
      rw [recon X1 hX1, recon X2 hX2, hGG, h2]
    · rintro ⟨⟨x, hx⟩, ⟨X', hX'⟩⟩
      have hform : (G x hx * fromBlocks 1 0 0 X')ᴴ * HH H' * (G x hx * fromBlocks 1 0 0 X') = HH H' := by
        calc _ = (fromBlocks 1 0 0 X' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A)ᴴ * ((G x hx)ᴴ * HH H' * G x hx) *
              fromBlocks 1 0 0 X' := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = HH H' := by rw [(hG x hx).1, form_block, hX']; rfl
      have hxe : (G x hx * fromBlocks 1 0 0 X') *ᵥ e₀ = x := by
        rw [← Matrix.mulVec_mulVec, block_mulVec_e₀, (hG x hx).2.2]
      refine ⟨⟨_, hform⟩, ?_⟩
      simp only [f]
      obtain ⟨_, hGG'⟩ := hGeq _ _ (form_col hform h00) hx hxe
      refine Prod.ext (Subtype.ext hxe) (Subtype.ext ?_)
      dsimp only
      rw [hGG', ← Matrix.mul_assoc, hinv, Matrix.one_mul, Matrix.toBlocks_fromBlocks₂₂]
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.ofBijective f hf)

end Formalism.HermitianLattices.Ext.L3.PinE
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomLocFOfVdZero
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace U0

open WA

omit [FiniteDimensional K V] in
theorem isLatIn_loc {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {P : Ideal (𝓞 K)}
    (hP : P.IsPrime) : IsLatIn (locRing P) h ⊤ (Formalism.HermitianLatticesTheory.loc (K := K) P L).toAddSubgroup := by
  refine ⟨fun _ _ => Submodule.mem_top, ?_, ?_, ?_⟩
  · intro a ha m hm
    exact smul_mem_loc hP ha hm
  · intro x hx y hy
    obtain ⟨s, hs, hsx⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp
      (show x ∈ Formalism.HermitianLatticesTheory.locS (Formalism.HermitianLatticesTheory.hcompl (K := K) P) L from hx)
    obtain ⟨t, ht, hty⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp
      (show y ∈ Formalism.HermitianLatticesTheory.locS (Formalism.HermitianLatticesTheory.hcompl (K := K) P) L from hy)
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hLi _ hsx _ hty)
    rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right, ← algebraMap_conjO] at hr
    have hcs := conjO_mem_hcompl hs
    have h1 := algebraMap_ne_zero_of_mem_hcompl hP hcs
    have h2 := algebraMap_ne_zero_of_mem_hcompl hP ht
    have e : h x y = algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K (conjO K s * t) := by
      rw [hr, map_mul]
      field_simp
    rw [e]
    exact div_mem_locRing hP r (mul_mem hcs ht)
  · intro x _
    obtain ⟨n, hn, hnx⟩ := Formalism.HermitianLatticesTheory.traceReal_mult L hL x
    refine ⟨(n : K), by exact_mod_cast hn, ?_⟩
    rw [Int.cast_smul_eq_zsmul]
    exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ L hnx

omit [FiniteDimensional K V] in
theorem isSD_loc {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) {P : Ideal (𝓞 K)} (hP : P.IsPrime)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h P L) :
    IsSD (locRing P) h ⊤ (Formalism.HermitianLatticesTheory.loc (K := K) P L).toAddSubgroup := by
  have h0 := isSelfDualMod_loc hL hP hu
  exact ⟨⟨fun _ _ => Submodule.mem_top, h0.smul_mem, h0.int, fun x _ => h0.span x⟩,
    fun x _ hx => h0.dual x hx⟩

omit [NumberField K] [StarRing K] [FiniteDimensional K V] in
theorem gmap_eq_of_iff {g : V ≃ₗ[K] V} {A B : Submodule (𝓞 K) V} (hg : ∀ v, v ∈ A ↔ g v ∈ B) :
    Formalism.HermitianLatticesTheory.gmap g A = B := by
  ext w
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (hg v).mp hv
  · intro hw
    exact ⟨g.symm w, (hg _).mpr (by rw [g.apply_symm_apply]; exact hw), g.apply_symm_apply w⟩

theorem exists_isASD_loc {h : V →ₗ⋆[K] V →ₗ[K] K} (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hv : vd h L (P.comap (algebraMap (𝓞 F) (𝓞 K))) = 1) {π : K} (hπ : IsUnif (locRing P) π)
    (h1 : ∀ z ∈ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))),
      Dv (locRing P) π (algebraMap (𝓞 K) K z))
    (h2 : ∀ z : 𝓞 K, Dv (locRing P) π (algebraMap (𝓞 K) K z * π⁻¹) →
      z ∈ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2) :
    ∃ z, IsASD (locRing P) π h ⊤ (Formalism.HermitianLatticesTheory.loc (K := K) P L).toAddSubgroup z := by
  have hPp := hP.isPrime
  have hb : BddAbove {e : ℕ | discrIdeal h L ≤ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ e} := by
    by_contra hnb
    unfold vd at hv
    rw [Nat.sSup_of_not_bddAbove hnb] at hv
    omega
  have hmem := Nat.sSup_mem (s := {e : ℕ | discrIdeal h L ≤
    extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ e}) ⟨0, by simp⟩ hb
  have hle : discrIdeal h L ≤ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) := by
    change discrIdeal h L ≤ _ ^ vd h L (P.comap (algebraMap (𝓞 F) (𝓞 K))) at hmem
    rwa [hv, pow_one] at hmem
  have hn2 : ¬ discrIdeal h L ≤ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2 := by
    intro hle2
    have h3 : 2 ≤ vd h L (P.comap (algebraMap (𝓞 F) (𝓞 K))) := le_csSup hb hle2
    omega
  unfold discrIdeal at hn2
  rw [Ideal.span_le, Set.not_subset] at hn2
  obtain ⟨z, ⟨x, hx, hz⟩, hzn⟩ := hn2
  refine exists_isASD_of_tuple (isHermSemilocal_locRing hK hP) hπ hs hd (isLatIn_loc hL hLi hPp) x
    (fun i => Formalism.HermitianLatticesTheory.locBasic_le_locS _ L (hx i)) ?_ ?_
  · intro hdv
    apply hzn
    apply h2
    rw [hz]
    exact hdv
  · intro t ht horth
    choose s hs' hst using fun i => Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp
      (show t i ∈ Formalism.HermitianLatticesTheory.locS (Formalism.HermitianLatticesTheory.hcompl (K := K) P) L from ht i)
    obtain ⟨g, -, hdet⟩ := LocF.exists_gram hLi (fun i => s i • t i) hst
    have hmem : g.det ∈ discrIdeal h L := Ideal.subset_span ⟨_, hst, hdet⟩
    have hdv := h1 _ (hle hmem)
    have e : (Matrix.of fun i j => h (s i • t i) (s j • t j)) =
        gram h fun i => algebraMap (𝓞 K) K (s i) • t i := by
      ext i j
      simp only [gram, Matrix.of_apply, algebraMap_smul]
    rw [hdet, e, gram_det_smul_orth horth, ← gram_det_orth horth] at hdv
    have hu : IsUnitIn (locRing P)
        (∏ i, star (algebraMap (𝓞 K) K (s i)) * algebraMap (𝓞 K) K (s i)) := by
      apply LocF.isUnitIn_prod
      intro i _
      refine LocF.isUnitIn_mul ?_ ?_
      · rw [← algebraMap_conjO, LocF.isUnitIn_algebraMap_iff hPp]
        exact conjO_mem_hcompl (hs' i)
      · rw [LocF.isUnitIn_algebraMap_iff hPp]
        exact hs' i
    have h3 := hdv.mul_left hu.2.2
    rwa [← mul_assoc, inv_mul_cancel₀ hu.1, one_mul] at h3

end U0

theorem exists_isom_locF_of_vd_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A B : Submodule (𝓞 K) V}
    (hA : Submodule.IsFullLattice K A) (hB : Submodule.IsFullLattice K B)
    (hAi : Formalism.HermitianLatticesTheory.IsIntegralLat h A) (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hvA : vd h A 𝔭 = 0) (hvB : vd h B 𝔭 = 0) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 A) = locF 𝔭 B := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have hda := LocF.aniso_of_totPosDef hd
  obtain ⟨π, hπ, -, -⟩ := U0.exists_isUnif hF hP
  rw [locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
  obtain ⟨g, hg, -, hgM⟩ := U0.sd_main (WA.isHermSemilocal_locRing hK hP) hπ hs hda _ ⊤ ⊤ _ _ 1
    le_rfl
    (U0.isSD_loc hA hP.isPrime ((isUnimodularAt_iff_vd hK hF hs hd hA hAi hP).mpr hvA))
    (U0.isSD_loc hB hP.isPrime ((isUnimodularAt_iff_vd hK hF hs hd hB hBi hP).mpr hvB))
    (one_mem _) (fun _ => ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩)
  exact ⟨g, hg, U0.gmap_eq_of_iff hgM⟩

theorem exists_isom_locF_of_vd_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A B : Submodule (𝓞 K) V}
    (hA : Submodule.IsFullLattice K A) (hB : Submodule.IsFullLattice K B)
    (hAi : Formalism.HermitianLatticesTheory.IsIntegralLat h A) (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hvA : vd h A 𝔭 = 1) (hvB : vd h B 𝔭 = 1) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 A) = locF 𝔭 B := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have hda := LocF.aniso_of_totPosDef hd
  obtain ⟨π, hπ, h1, h2⟩ := U0.exists_isUnif hF hP
  rw [locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
  obtain ⟨z₁, hM⟩ := U0.exists_isASD_loc hK hs hda hA hAi hP hvA hπ h1 h2
  obtain ⟨z₂, hN⟩ := U0.exists_isASD_loc hK hs hda hB hBi hP hvB hπ h1 h2
  obtain ⟨g, hg, -, hgM⟩ := U0.asd_main (WA.isHermSemilocal_locRing hK hP) hπ hs hda _ ⊤ ⊤ _ _
    z₁ z₂ 1 le_rfl hM hN
    (one_mem _) (fun _ => ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩)
  exact ⟨g, hg, U0.gmap_eq_of_iff hgM⟩

end Formalism.HermitianLattices.Ext.L3
end
end

