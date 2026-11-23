module

public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.Bundle0002
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JNoEig
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.FinitelyGeneratedModPow

@[expose] public section

-- bundled from Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JArith
section
noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Car}

def NegOneNorm (D : Car) : Prop :=
  ∀ m : ℕ, 0 < m → ∃ lam s : 𝓞 D.host.E, star (s : D.host.E) = (s : D.host.E) ∧
    star (lam : D.host.E) * (lam : D.host.E) = -1 + (m : D.host.E) * (s : D.host.E)

def mulO (N N' : ℕ) (r : D.host.E) : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N' where
  toFun z := fun τ i j => TaylorLogMetric.embT D τ r * z τ i j
  map_add' x y := by funext τ i j; exact mul_add _ _ _
  map_smul' c x := by funext τ i j; exact mul_left_comm _ _ _

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Cd.Base D cc δ)

theorem mul_integer_mem_base_lattice {N N' : ℕ} (r : 𝓞 D.host.E) {x : TaylorLogMetric.VC D N N'} (hx : x ∈ La0 B N N') :
    mulO N N' (r : D.host.E) x ∈ La0 B N N' := by
  have hle : La0 B N N' ≤ (La0 B N N').comap (mulO N N' (r : D.host.E)).toAddMonoidHom := by
    show TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') ≤
      (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')).comap (mulO N N' (r : D.host.E)).toAddMonoidHom
    rw [TaylorLogMetric.La, AddSubgroup.closure_le]
    rintro _ ⟨w, hw, A, hA, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    apply AddSubgroup.subset_closure
    refine ⟨w, hw, r • A, Submodule.smul_mem _ r hA, ?_⟩
    funext τ i j
    simp [mulO, TaylorLogMetric.embV, TaylorLogMetric.tor0, Algebra.smul_def, map_mul]
    ring
  exact hle hx

theorem star_int (r : 𝓞 D.host.E) : ∃ r' : 𝓞 D.host.E, (r' : D.host.E) = star (r : D.host.E) :=
  ⟨⟨star (r : D.host.E), by
    have h := (NumberField.RingOfIntegers.isIntegral_coe r).map (starRingEnd D.host.E).toIntAlgHom
    first
      | exact (mem_integralClosure_iff ℤ D.host.E).mpr h
      | exact h⟩, rfl⟩

theorem mulO_phi {N N' : ℕ} (r : D.host.E) (γ : Matrix.unitaryGroup (Fin N) D.host.E)
    (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (x : TaylorLogMetric.VC D N N') :
    mulO N N' r (phiU γ γ' x) = phiU γ γ' (mulO N N' r x) := by
  funext τ i j
  show TaylorLogMetric.embT D τ r * (gM (γ' : Matrix (Fin N') (Fin N') D.host.E) τ * Matrix.of (x τ) *
      (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) i j =
    (gM (γ' : Matrix (Fin N') (Fin N') D.host.E) τ * Matrix.of (fun i j => TaylorLogMetric.embT D τ r * x τ i j) *
      (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) i j
  have h1 : Matrix.of (fun i j => TaylorLogMetric.embT D τ r * x τ i j) = TaylorLogMetric.embT D τ r • Matrix.of (x τ) := by
    ext a b
    simp
  rw [h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

theorem mulO_adj (A : ℝ) {N N' : ℕ} (r : D.host.E) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (mulO N N' r x) y = Ker.formV A D.what₂.Tau N N' x (mulO N N' (star r) y) := by
  simp only [Formalism.L2.Ker.formV, LinearMap.mk₂'ₛₗ_apply, mulO, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, embT_star', Complex.star_def, Complex.conj_conj]
  ring

theorem gaussRow_of (hS : B.StdOK) (hL : B.LatAll) (hNeg : NegOneNorm D) : GaussRow B := by
  intro N γ Ae₁ hN hA₁ S hS₁
  have hfix₁ : ∀ y : TaylorLogMetric.VC D N 1, (phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1).symm y = y → y = 0 := by
    intro y hy
    apply Ae₁.injective
    rw [hA₁, hy, sub_self, map_zero]
  have hfix : ∀ x : TaylorLogMetric.VC D N 2, (phiU γ 1 : TaylorLogMetric.VC D N 2 ≃ₗ[ℂ] TaylorLogMetric.VC D N 2).symm x = x → x = 0 := by
    intro x hx
    apply (rowE D N 2).injective
    funext i
    rw [map_zero]
    refine hfix₁ _ ?_
    rw [← symm_coord (rowE D N 2) _ _ (map_row γ), hx]
  obtain ⟨Ae, hA⟩ := exists_cay (phiU γ 1 : TaylorLogMetric.VC D N 2 ≃ₗ[ℂ] TaylorLogMetric.VC D N 2) hfix
  have c : Copies (rowE D N 2) (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N 2)
      (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N 1) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ))
      (La0 B N 2) (La0 B N 1) (phiU γ 1) Ae (phiU γ 1) Ae₁ :=
    { form := form_row _ N 2
      char := al_row B hS N 2
      lat := lat_row B N 2
      map := map_row γ
      cay := fun x i => by
        rw [hA, hA₁, map_sub, Pi.sub_apply, symm_coord (rowE D N 2) _ _ (map_row γ)] }
  have hal0 : TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (0 : TaylorLogMetric.VC D N 1) = 1 := by
    unfold TaylorLogMetric.al TaylorLogMetric.Hf
    simp
  have hU₁ := c.unitaryData₁ 0 (unitaryData hL hN (by decide) γ 1 Ae hA) (formV_herm' _ _ _ _)
    (formV_pos (area_pos' B) _ _ _) (phiL_isom _ _ _ _ _ _ _) hA₁ hal0 (al_phi _ _ _ _ _ _)
  have hcard : 0 < S.card := by
    obtain ⟨x, hx, -⟩ := hS₁.2.2 0 (AddSubgroup.zero_mem _)
    exact Finset.card_pos.mpr ⟨x, hx⟩
  obtain ⟨lam, s, hs, hrel⟩ := hNeg (4 * S.card) (by omega)
  obtain ⟨lam', hlam'⟩ := star_int lam
  have hM : Multipliers (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N 1) (La0 B N 1) (phiU γ 1)
      (mulO N 1 (lam : D.host.E)) (mulO N 1 (star (lam : D.host.E))) (mulO N 1 (s : D.host.E)) S.card :=
    { lΛ := fun x hx => mul_integer_mem_base_lattice B lam hx
      l'Λ := fun x hx => by rw [← hlam']; exact mul_integer_mem_base_lattice B lam' hx
      sΛ := fun x hx => mul_integer_mem_base_lattice B s hx
      lδ := mulO_phi _ γ 1
      l'δ := mulO_phi _ γ 1
      sδ := mulO_phi _ γ 1
      adj := mulO_adj _ _
      sadj := fun x y => by rw [mulO_adj, hs]
      rel := fun x => by
        funext τ i j
        show TaylorLogMetric.embT D τ (star (lam : D.host.E)) * (TaylorLogMetric.embT D τ (lam : D.host.E) * x τ i j) =
          -x τ i j + (4 * S.card) • (TaylorLogMetric.embT D τ (s : D.host.E) * x τ i j)
        rw [← mul_assoc, ← map_mul, hrel, map_add (f := _), map_neg, map_one, map_mul, map_natCast, nsmul_eq_mul]
        ring }
  exact gauss_sq hU₁ hM (fun x hx => card_smul_mem hS₁ hx)
    (fun x hx => alpha_mult hM (Real.sqrt D.host.d / 2) _ (fun _ => rfl) (B.qInt0 hS N 1) hx) hS₁

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
end
end

-- bundled from Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SecondConstantOfTrianglesData
section
noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Cd.Base D cc δ}

theorem first_constant_of_triangles_data (hS : B.StdOK) (hL : B.LatAll) (hTL : Tr0L D B.tor) (hG : GaussRow B)
    (hLat : ∀ N N', Even N → Even N' → Lat0IsLat B N N') (hSp : ∀ N N', Even N → Even N' → B.ThZeroSpans N N') : J1 B := by
  intro N N' γ hN hN'
  obtain ⟨γ₁, γ₂, rfl, h1, h2⟩ := split_host D γ
  have h0 := Formalism.L2.Ker.Cd.Base.thZeroMem B hS N N'
  exact J1at_mul hL hTL hN hN' h0 γ₁ γ₂
    (J1at_of_ne hS hL hG hN hN' (hLat N N' hN hN') (hSp N N' hN hN') γ₁ h1)
    (J1at_of_ne hS hL hG hN hN' (hLat N N' hN hN') (hSp N N' hN hN') γ₂ h2)

theorem second_constant_of_triangles_data (hS : B.StdOK) (hL : B.LatAll) (hTR : Tr0R D B.tor) (hG : GaussRow B)
    (hLat : ∀ N N', Even N → Even N' → Lat0IsLat B N N') (hSp : ∀ N N', Even N → Even N' → B.ThZeroSpans N N') : J2 B := by
  intro N N' γ' hN hN'
  obtain ⟨γ₁, γ₂, rfl, h1, h2⟩ := split_host D γ'
  have h0 := Formalism.L2.Ker.Cd.Base.thZeroMem B hS N N'
  have key := J2at_mul hL hTR hN hN' h0 γ₁ γ₂
    (J2at_of_ne hS hL hG hN hN' (hLat N N' hN hN') (hSp N N' hN hN') γ₁ h1)
    (J2at_of_ne hS hL hG hN hN' (hLat N N' hN hN') (hSp N N' hN hN') γ₂ h2)
  have hhalf : B.thHalf N N' (StandardLatticesGL3.stdL D N) = B.thZero N N' := by
    unfold Formalism.L2.Ker.Cd.Base.thHalf
    exact iopSelf D B.tor N N' _ _ (Formalism.L2.Ker.Cd.mem_ThSp_of D B.tor _ _ h0)
  unfold J2at at key
  unfold Formalism.L2.Ker.Cd.Base.thMoved
  rw [hhalf]
  exact key

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
end
end

-- bundled from Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.ZeroInjectionMemFourthPower
section
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

section Gen

variable {n : Type} [Fintype n]

def inj0 (n : Type) : (n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ) where
  toFun x := fun w => if w.1 = 0 then x w.2 else 0
  map_add' x y := by funext w; by_cases h : w.1 = 0 <;> simp [h]
  map_smul' c x := by funext w; by_cases h : w.1 = 0 <;> simp [h]

def sl0 (n : Type) : (Fin 4 × n → ℂ) →ₗ[ℂ] (n → ℂ) where
  toFun z := slice 0 z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem slice_zero_injection (x : n → ℂ) (a : Fin 4) : slice a (inj0 n x) = if a = 0 then x else 0 := by
  funext i
  by_cases h : a = 0 <;> simp [slice, inj0, h]

theorem zero_injection_mem_fourth_power (ΛM : AddSubgroup (n → ℂ)) {x : n → ℂ} (hx : x ∈ ΛM) : inj0 n x ∈ pow4 ΛM := by
  intro a
  rw [slice_zero_injection]
  split_ifs
  · exact hx
  · exact ΛM.zero_mem

theorem is_lattice_of_fourth_power (ΛM : AddSubgroup (n → ℂ)) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (h : IsLat (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM))) : IsLat ΛM := by
  obtain ⟨hd, hs⟩ := h
  refine ⟨?_, ?_⟩
  · haveI := hd
    let φ : ΛM → imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM) :=
      fun x => ⟨g (inj0 n x), ⟨inj0 n x, zero_injection_mem_fourth_power ΛM x.2, rfl⟩⟩
    have hφc : Continuous φ := by
      apply Continuous.subtype_mk
      exact ((g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)).comp (inj0 n)).continuous_of_finiteDimensional.comp
        continuous_subtype_val
    have hφi : Function.Injective φ := by
      intro x y hxy
      have h1 := congrArg Subtype.val hxy
      have h2 := g.injective h1
      apply Subtype.ext
      have h3 := congrArg (slice 0) h2
      rwa [slice_zero_injection, slice_zero_injection, if_pos rfl, if_pos rfl] at h3
    exact DiscreteTopology.of_continuous_injective hφc hφi
  · rw [eq_top_iff]
    intro x _
    let G : (Fin 4 × n → ℂ) →ₗ[ℝ] (n → ℂ) := ((sl0 n).comp g.symm.toLinearMap).restrictScalars ℝ
    have hG : ∀ y ∈ (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM) : Set _), G y ∈ ΛM := by
      rintro _ ⟨z, hz, rfl⟩
      show slice 0 (g.symm (g z)) ∈ ΛM
      rw [g.symm_apply_apply]
      exact hz 0
    have hmap : Submodule.map G (Submodule.span ℝ
        (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 ΛM) : Set _)) ≤
        Submodule.span ℝ (ΛM : Set (n → ℂ)) := by
      rw [Submodule.map_span]
      exact Submodule.span_mono (by rintro _ ⟨y, hy, rfl⟩; exact hG y hy)
    rw [hs, Submodule.map_top] at hmap
    apply hmap
    refine ⟨g (inj0 n x), ?_⟩
    show slice 0 (g.symm (g (inj0 n x))) = x
    rw [g.symm_apply_apply, slice_zero_injection, if_pos rfl]

def putL (n : Type) (N N' : ℕ) (k : Fin N' × Fin N) : (n → ℂ) →ₗ[ℂ] (n → Fin N' → Fin N → ℂ) where
  toFun x := fun τ i j => if (i, j) = k then x τ else 0
  map_add' x y := by funext τ i j; by_cases h : (i, j) = k <;> simp [h]
  map_smul' c x := by funext τ i j; by_cases h : (i, j) = k <;> simp [h]

theorem putL_mem (ΛM : AddSubgroup (n → ℂ)) (N N' : ℕ) (k : Fin N' × Fin N) {x : n → ℂ} (hx : x ∈ ΛM) :
    putL n N N' k x ∈ Ker.powLat ΛM N N' := by
  intro i j
  by_cases h : (i, j) = k
  · have e : (fun τ => putL n N N' k x τ i j) = x := by
      funext τ
      simp [putL, h]
    rw [e]
    exact hx
  · have e : (fun τ => putL n N N' k x τ i j) = 0 := by
      funext τ
      simp [putL, h]
    rw [e]
    exact ΛM.zero_mem

theorem sum_putL (N N' : ℕ) (z : n → Fin N' → Fin N → ℂ) :
    z = ∑ k : Fin N' × Fin N, putL n N N' k (fun τ => z τ k.1 k.2) := by
  funext τ i j
  simp [putL, Finset.sum_apply]

theorem isLat_powLat (ΛM : AddSubgroup (n → ℂ)) (h : IsLat ΛM) (N N' : ℕ) : IsLat (Ker.powLat ΛM N N') := by
  obtain ⟨hd, hs⟩ := h
  refine ⟨?_, ?_⟩
  · haveI := hd
    let ψ : Ker.powLat ΛM N N' → (Fin N' × Fin N → ΛM) :=
      fun z k => ⟨fun τ => z.1 τ k.1 k.2, z.2 k.1 k.2⟩
    have hψc : Continuous ψ := by
      apply continuous_pi
      intro k
      apply Continuous.subtype_mk
      apply continuous_pi
      intro τ
      have hc : Continuous (fun z : Ker.powLat ΛM N N' => (z : n → Fin N' → Fin N → ℂ)) :=
        continuous_subtype_val
      have hc1 : Continuous (fun z : Ker.powLat ΛM N N' => (z : n → Fin N' → Fin N → ℂ) τ) :=
        (continuous_apply τ).comp hc
      have hc2 : Continuous (fun z : Ker.powLat ΛM N N' => (z : n → Fin N' → Fin N → ℂ) τ k.1) :=
        (continuous_apply k.1).comp hc1
      exact (continuous_apply k.2).comp hc2
    have hψi : Function.Injective ψ := by
      intro x y hxy
      apply Subtype.ext
      funext τ i j
      have h1 := congrArg (fun f => ((f (i, j) : ΛM) : n → ℂ) τ) hxy
      exact h1
    exact DiscreteTopology.of_continuous_injective hψc hψi
  · rw [eq_top_iff]
    intro z _
    rw [sum_putL N N' z]
    refine Submodule.sum_mem _ fun k _ => ?_
    have hk : (fun τ => z τ k.1 k.2) ∈ Submodule.span ℝ (ΛM : Set (n → ℂ)) := by
      rw [hs]
      trivial
    have hmap : Submodule.map ((putL n N N' k).restrictScalars ℝ) (Submodule.span ℝ (ΛM : Set (n → ℂ))) ≤
        Submodule.span ℝ (Ker.powLat ΛM N N' : Set _) := by
      rw [Submodule.map_span]
      exact Submodule.span_mono (by rintro _ ⟨y, hy, rfl⟩; exact putL_mem ΛM N N' k hy)
    exact hmap ⟨_, hk, rfl⟩

end Gen

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {B : Cd.Base D cc δ}

theorem isLat_lamM (hS : B.StdOK) : IsLat B.lamM := by
  unfold Formalism.L2.Ker.Cd.Base.StdOK Formalism.L2.Ker.StdOK at hS
  have hI : IsLat (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) :=
    Formalism.L2.Th1.H.KR.isLat_of_comm (Formalism.L2.Th1.H.KR.isLat_stdLat B.L _) hS.idx₂ hS.idx₁
  exact is_lattice_of_fourth_power B.lamM B.gC hI

theorem lat0IsLat (hS : B.StdOK) (N N' : ℕ) : Lat0IsLat B N N' := by
  unfold Lat0IsLat La0
  rw [Formalism.L2.Ker.Cd.Lat0 (D := D) (N := N) (N' := N') cc δ]
  exact isLat_powLat _ (isLat_lamM hS) N N'

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
end
end

