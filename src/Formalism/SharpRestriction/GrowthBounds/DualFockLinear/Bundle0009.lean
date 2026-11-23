module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle0008
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.SubstSPtrue

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.DualWeylZeroConst
section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.MainNotions.G.LatticeSystems (lb_D lb_D_det)

section Ext

variable {Kf : Type} [Field Kf] {n' m : ℕ} {A : Finset (Fin n')} {X XT sp : Fin n' → Fin (m + 1) → ℤ}

theorem exists_ext (G : Module.Dual Kf (Vsp Kf X)) :
    ∃ γ : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₗ[Kf] Kf, ∀ Q : Vsp Kf X, γ (Q : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = G Q := by
  obtain ⟨γ, hγ⟩ := LinearMap.exists_extend G
  exact ⟨γ, fun Q => by rw [← hγ]; rfl⟩

def extD (G : Module.Dual Kf (Vsp Kf X)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₗ[Kf] Kf := (exists_ext G).choose

theorem extD_spec (G : Module.Dual Kf (Vsp Kf X)) (Q : Vsp Kf X) : extD G (Q : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = G Q :=
  (exists_ext G).choose_spec Q

def peelMap (hP : Peel A X XT sp) (c : Kf) (G : Module.Dual Kf (Vsp Kf sp)) : Vsp Kf X →ₗ[Kf] Vsp Kf XT :=
  (c • slice A (extD G)).restrict (fun u hu => Submodule.smul_mem _ _ (slice_V hP _ u hu))

theorem peelMap_coe (hP : Peel A X XT sp) (c : Kf) (G : Module.Dual Kf (Vsp Kf sp)) (u : Vsp Kf X) :
    ((peelMap hP c G u : Vsp Kf XT) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = c • slice A (extD G) (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := rfl

variable {O : Type} [CommRing O] [Algebra O Kf]

theorem peel_Hten (hP : Peel A X XT sp) (hdT : IsDominant XT) (hdsp : IsDominant sp)
    (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf))
    (hΛ : ∀ s, ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧ Λ s = colSpan O g)
    (c0 c : Kf) (G : Module.Dual Kf (Vsp Kf sp))
    (hG : ∀ Qv : Vsp Kf sp, (Qv : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O sp Λ → ∃ a : O, G Qv = c * algebraMap O Kf a)
    (u : Vsp Kf X) (hu : (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O X Λ) :
    ∃ yv : Vsp Kf XT, (yv : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O XT Λ ∧ peelMap hP c0 G u = (c0 * c) • yv := by
  obtain ⟨y, hy, he⟩ := slice_Hten hP Λ (extD G) c (fun Q hQ => by
      obtain ⟨a, ha⟩ := hG ⟨Q, Hten_le_V hdsp Λ hΛ Q hQ⟩ hQ
      exact ⟨a, by rw [← ha]; exact extD_spec G ⟨Q, _⟩⟩) u hu
  refine ⟨⟨y, Hten_le_V hdT Λ hΛ y hy⟩, hy, Subtype.ext ?_⟩
  rw [peelMap_coe, he, smul_smul]
  rfl

end Ext

section Lat

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem Re'_le_scale (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (X : Fin n' → Fin (m + 1) → ℤ)
    (hd : IsDominant X) (e : Edge W Qq (m + 1)) (he : IsEdge p n' r e) (M : ℕ) (hM : ordMax r X ≤ M) :
    Re' p ι σ w r X e ≤ scale (algebraMap O Kf w ^ (-(M : ℤ))) (dualLat O Kf (HL (O := O) ι σ X e.tgt)) := by
  obtain ⟨I, hI, x, π, _, c2, _, c4, c4', _, c7⟩ := edge_lattice_adapted_basis h m r X hd e he
  have hw := w_ne_zero h
  have hp0 : (p : Kf) ≠ 0 := by rw [Formalism.L2.G.Model.p_eq h]; exact pow_ne_zero _ hw
  rw [← c7, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine mem_scale.2 ⟨w ^ ((M : ℤ) - order r X (π i)).toNat • (((p : Kf) ^ π i)⁻¹ • x.coord i), ?_, ?_⟩
  · rw [← c2, Formalism.L2.G.Model.dualLat_span x (fun i => (p : Kf) ^ π i) (fun i => zpow_ne_zero _ hp0)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · have h1 := c4' i
    rw [← algebraMap_smul Kf (w ^ ((M : ℤ) - order r X (π i)).toNat), smul_smul, smul_smul, map_pow, ← zpow_natCast,
      Int.toNat_of_nonneg (by omega), ← zpow_add₀ hw]
    show _ = ((algebraMap O Kf) w ^ (-order r X (π i)) * (p : Kf) ^ (-π i)) • x.coord i
    rw [zpow_neg (p : Kf)]
    congr 3
    ring

variable {m : ℕ} {A : Finset (Fin n')} {X XT sp : Fin n' → Fin (m + 1) → ℤ}

theorem p_zpow (h : HidaSetting p n' W Qq O Kf ι σ j w) (z : ℤ) : (p : Kf) ^ z = algebraMap O Kf w ^ (2 * z) := by
  rw [Formalism.L2.G.Model.p_eq h, ← zpow_natCast, ← zpow_mul]
  norm_num

theorem peel_Re (h : HidaSetting p n' W Qq O Kf ι σ j w) (hP : Peel A X XT sp) (hX : X = XT + sp) (hdT : IsDominant XT)
    (hdsp : IsDominant sp) (r : ℕ) (e' : Edge W Qq (m + 1)) (he' : IsEdge p n' r e') (N : ℤ)
    (G : Module.Dual Kf (Vsp Kf sp))
    (hG : ∀ Q ∈ Re p ι σ w r sp e', ∃ a : O, be p r sp Q G = algebraMap O Kf w ^ N * algebraMap O Kf a) :
    ∀ u ∈ Re p ι σ w r X e',
      peelMap hP ((p : Kf) ^ Ar r sp) G u ∈ scale (algebraMap O Kf w ^ N) (Re p ι σ w r XT e') := by
  intro u hu
  have hw := w_ne_zero h
  have hAr : Ar r X = Ar r XT + Ar r sp := by rw [hX]; exact Ar_add r _ _
  obtain ⟨gs, hgs, _, h2, _⟩ := Formalism.L2.G.Model.edgeLat h m r e' he'
  have hΛ : ∀ s : Fin n', ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧
      LeAt p ι σ w s.val e' = colSpan O g := fun s =>
    ⟨_, by rw [Matrix.det_mul]; exact (hgs _).mul (lb_D_det _ _ _ hw), h2 s.val⟩
  obtain ⟨u0, hu0, rfl⟩ := mem_scale.1 hu
  have hu0' : ((u0 : Vsp Kf X) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O X (fun s => LeAt p ι σ w s.val e') := hu0
  obtain ⟨yv, hy, he⟩ := peel_Hten hP hdT hdsp (fun s => LeAt p ι σ w s.val e') hΛ ((p : Kf) ^ Ar r sp)
    (algebraMap O Kf w ^ (N - Ar r sp)) G (by
      intro Qv hQv
      obtain ⟨a, ha⟩ := hG (algebraMap O Kf w ^ (-Ar r sp) • Qv) (mem_scale.2 ⟨Qv, hQv, rfl⟩)
      refine ⟨a, ?_⟩
      rw [be_smulK_left] at ha
      unfold be at ha
      rw [map_smul, smul_eq_mul, p_zpow h, ← mul_assoc, ← zpow_add₀ hw] at ha
      have e1 : -Ar r sp + 2 * Ar r sp = Ar r sp := by ring
      rw [e1] at ha
      rw [zpow_sub₀ hw, div_mul_eq_mul_div, eq_div_iff (zpow_ne_zero _ hw), mul_comm]
      exact ha) u0 hu0'
  rw [map_smul, he]
  refine mem_scale.2 ⟨algebraMap O Kf w ^ (-Ar r XT) • yv, mem_scale.2 ⟨yv, hy, rfl⟩, ?_⟩
  rw [smul_smul, smul_smul, p_zpow h, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, hAr]
  congr 2
  ring

theorem peel_HL (hP : Peel A X XT sp) (hdT : IsDominant XT) (hdsp : IsDominant sp)
    (L : Submodule W (Fin (m + 1) → Qq))
    (hL : ∀ s : Fin n', ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧ extO O ι σ s.val L = colSpan O g)
    (c0 c : Kf) (G : Module.Dual Kf (Vsp Kf sp))
    (hG : ∀ Q ∈ HL (O := O) ι σ sp L, ∃ a : O, G Q = c * algebraMap O Kf a) :
    ∀ u ∈ HL (O := O) ι σ X L, peelMap hP c0 G u ∈ scale (c0 * c) (HL (O := O) ι σ XT L) := by
  intro u hu
  obtain ⟨yv, hy, he⟩ := peel_Hten hP hdT hdsp (fun s => extO O ι σ s.val L) hL c0 c G (fun Qv hQv => hG Qv hQv) u hu
  exact mem_scale.2 ⟨yv, hy, he.symm⟩

end Lat

theorem dualWeyl_zero_const {R : Type} [CommRing R] {r n : ℕ} (F : MvPolynomial (Fin r × Fin n) R)
    (hF : F ∈ dualWeyl R r n 0) : F = C (AddMonoidAlgebra.coeff F 0) := by
  classical
  have h1 : IsWeightedHomogeneous (colW r n) F 0 := (mem_dualWeyl_iff.1 hF).1
  ext e
  rw [coeff_C]
  split_ifs with he
  · rw [he]
  · apply h1.coeff_eq_zero
    intro hwt
    apply he
    symm
    ext v
    have h2 := congrFun hwt v.2
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at h2
    by_contra hv
    have h3 := (Finset.sum_eq_zero_iff.1 h2) v (Finsupp.mem_support_iff.2 (by simpa using hv))
    simp [colW] at h3
    exact hv (by simpa using h3)

end Formalism.MainNotions.TestSideCounting
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.LaTwInvT
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.Pf14 Formalism.MainNotions.SourceCleaning
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det H0_eq_twisted_nabla la_indep)
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Lin_smul Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol VS
  letterWt_anti flat_lam tensor_lattice_twist_eq edgeLat_of la_tw_mul la_tw_transpose la_tw_inv dE invT_mul_D dual_edgeBasis w_ne p_eq
  pQ_ne kapR kapR_alg lift_eq Bm Bm_eq Mx Mx_det Avec pol_iff thF flat_Ar)
open Formalism.L2.G.Model.TS

section

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ} {d : Fin n' → ℕ}

theorem HL_iff (hS : HidaSetting p n' W Qq O Kf ι σ j w) (ℓ : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hℓ : IsUnit ℓ.det)
    (u : ↥(Vsp Kf (flW (m := m) d))) :
    u ∈ HL (O := O) ι σ (flW d) (colSpan W ℓ) ↔
      (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ LatM O d (fun s => la_tw ι σ s.val ℓ) := by
  show (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
    Hten O (flW d) (fun s => extO O ι σ s.val (colSpan W ℓ)) ↔ _
  rw [Hten_flW, tensor_lattice_twist_eq hS m (vecE n') d (fun x => x) ℓ hℓ]
  rfl

theorem HLe_iff (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ) (e : Edge W Qq (m + 1))
    (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsEdgeBasis p r e b) (u : ↥(Vsp Kf (flW (m := m) d))) :
    u ∈ HLe p ι σ w (flW d) e ↔
      (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
        LatM O d (fun s => la_tw ι σ s.val b * lb_D (m + 1) r (algebraMap O Kf w)) := by
  show (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
    Hten O (flW d) (fun s => LeAt p ι σ w s.val e) ↔ _
  have := hS.frac_O
  have e1 : (fun x : Fin n' => H0 O m (letterWt m (d x) (vecE n' x)) (LeAt p ι σ w x.val e)) =
      fun s => nablaLTw O Kf m (letterWt m (d s) (vecE n' s))
        (la_tw ι σ s.val b * lb_D (m + 1) r (algebraMap O Kf w)) := by
    funext x
    rw [(edgeLat_of hS m r e b hb).2.1, H0_eq_twisted_nabla (la_indep (IsFractionRing.injective O Kf)) _ _ (letterWt_anti _ _ _) _
      (by rw [Matrix.det_mul]; exact (la_tw_det _ _ _ _ hb.1).mul (lb_D_det _ _ _ (w_ne hS)))]
  rw [Hten_flW, e1]
  rfl

theorem la_tw_invT (s : ℕ) (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsUnit b.det) :
    la_tw ι σ s ((b⁻¹).transpose) = ((la_tw ι σ s b)⁻¹).transpose := by
  rw [la_tw_transpose, la_tw_inv _ _ hb]

theorem la_tw_dE (s r : ℕ) : la_tw ι σ s (dE (m + 1) r ((p : ℕ) : Qq)) = dE (m + 1) r ((p : ℕ) : Kf) := by
  ext a c
  simp only [la_tw, dE, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem dualM (hS : HidaSetting p n' W Qq O Kf ι σ j w) (s r : ℕ) (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (hb : IsUnit b.det) :
    la_tw ι σ s ((b⁻¹).transpose * dE (m + 1) r ((p : ℕ) : Qq)) * lb_D (m + 1) r (algebraMap O Kf w) =
      ((la_tw ι σ s b * lb_D (m + 1) r (algebraMap O Kf w))⁻¹).transpose := by
  have hω := w_ne hS
  have hp : ((p : ℕ) : Kf) = (algebraMap O Kf w) ^ 2 := by rw [← map_pow, hS.w_sq, map_natCast]
  rw [la_tw_mul, la_tw_invT s b hb, la_tw_dE, Matrix.mul_inv_rev, Matrix.transpose_mul, mul_assoc]
  congr 1
  simp only [dE, lb_D, Matrix.diagonal_mul_diagonal, Matrix.inv_diagonal, Matrix.diagonal_transpose]
  congr 1
  funext a
  have hu : IsUnit (fun a : Fin (m + 1) => if a.val < r then (algebraMap O Kf w)⁻¹ else (1 : Kf)) := by
    rw [Pi.isUnit_iff]
    intro a
    split_ifs
    · exact isUnit_iff_ne_zero.mpr (inv_ne_zero hω)
    · exact isUnit_one
  have hinv := congrFun (Ring.inverse_mul_cancel _ hu) a
  rw [Pi.mul_apply, Pi.one_apply] at hinv
  rw [eq_inv_of_mul_eq_one_left hinv]
  split_ifs with h
  · rw [inv_inv, hp]; field_simp
  · simp

variable (thK : ↥(Pol Kf (ι := Fin n') (m + 1) d) ≃ₗ[Kf] ↥(Vsp Kf (flW (m := m) d)))

theorem FD_edge (hS : HidaSetting p n' W Qq O Kf ι σ j w) (hm : 1 ≤ m)
    (hthK : ∀ P, ((thK P : ↥(Vsp Kf (flW (m := m) d))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecE n') (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf))
    (κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) d) (r : ℕ) (e : Edge W Qq (m + 1))
    (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsEdgeBasis p r e b) (i : ℤ)
    (y : ↥(Vsp Kf (flW (m := m) d)))
    (hy : y ∈ scale (algebraMap O Kf w ^ i) (Re p ι σ w r (flW d) e.dual)) :
    TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) y ∈
      scale (algebraMap O Kf w ^ i) (Re' p ι σ w r (flW d) e) := by
  obtain ⟨y1, hy1, rfl⟩ := mem_scale.1 hy
  obtain ⟨y0, hy0, rfl⟩ := mem_scale.1 hy1
  refine mem_scale.2 ⟨_, mem_scale.2 ⟨TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) y0, ?_, rfl⟩, ?_⟩
  · intro u hu
    refine sandwich thK hm hthK p κ hMD (fun s => la_tw ι σ s.val b * lb_D (m + 1) r (algebraMap O Kf w))
      (fun s => by rw [Matrix.det_mul]; exact (la_tw_det _ _ _ _ hb.1).mul (lb_D_det _ _ _ (w_ne hS))) u y0
      ((HLe_iff hS r e b hb u).1 hu) ?_
    have h1 := (HLe_iff hS r e.dual _ (dual_edgeBasis p r (pQ_ne hS) e b hb) y0).1 hy0
    have e1 : (fun s : Fin n' => la_tw ι σ s.val ((b⁻¹).transpose * dE (m + 1) r ((p : ℕ) : Qq)) *
        lb_D (m + 1) r (algebraMap O Kf w)) =
        fun s => ((la_tw ι σ s.val b * lb_D (m + 1) r (algebraMap O Kf w))⁻¹).transpose :=
      funext fun s => dualM hS s.val r b hb.1
    rw [e1] at h1
    exact h1
  · rw [map_smul, map_smul]

theorem FD_HL (hS : HidaSetting p n' W Qq O Kf ι σ j w) (hm : 1 ≤ m)
    (hthK : ∀ P, ((thK P : ↥(Vsp Kf (flW (m := m) d))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecE n') (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf))
    (κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) d)
    (ℓ : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hℓ : IsUnit ℓ.det) (c : Kf)
    (y : ↥(Vsp Kf (flW (m := m) d)))
    (hy : y ∈ scale c (HL (O := O) ι σ (flW d) (colSpan W ((ℓ⁻¹).transpose)))) :
    TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) y ∈
      scale c (dualLat O Kf (HL (O := O) ι σ (flW d) (colSpan W ℓ))) := by
  obtain ⟨y0, hy0, rfl⟩ := mem_scale.1 hy
  refine mem_scale.2 ⟨TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) y0, ?_, by rw [map_smul]⟩
  intro u hu
  refine sandwich thK hm hthK p κ hMD (fun s => la_tw ι σ s.val ℓ) (fun s => la_tw_det _ _ _ _ hℓ) u y0
    ((HL_iff hS ℓ hℓ u).1 hu) ?_
  have hℓt : IsUnit ((ℓ⁻¹).transpose).det := Formalism.L2.G.Model.det_invT ℓ hℓ
  have h1 := (HL_iff hS _ hℓt y0).1 hy0
  have e1 : (fun s : Fin n' => la_tw ι σ s.val ((ℓ⁻¹).transpose)) = fun s => ((la_tw ι σ s.val ℓ)⁻¹).transpose :=
    funext fun s => la_tw_invT s.val ℓ hℓ
  rw [e1] at h1
  exact h1

end

end Formalism.MainNotions.TestSideCounting
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.NormalDegreeZeroMul
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.G.WittFrameLocaliserOrders
open Formalism.L2.G.Model (Lin)

section Zero

variable {R : Type} [CommRing R] {n' k : ℕ}

theorem normal_degree_zero_one (r : ℕ) : (1 : MvPolynomial (TV n' k) R) ∈ NDsub R n' k r 0 := by
  rw [NDsub, MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hm0 : m = 0 := by
    by_contra hne
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff, MvPolynomial.coeff_one, if_neg (Ne.symm hne)] at hm
    exact hm rfl
  subst hm0
  simp [normDeg]

private lemma normDeg_add' {r : ℕ} (a b : TV n' k →₀ ℕ) : normDeg r (a + b) = normDeg r a + normDeg r b := by
  classical
  unfold normDeg
  exact Finsupp.sum_add_index' (h := fun v c => if IsNormal r v then c else 0) (fun v => by simp)
    (fun v c₁ c₂ => by split_ifs <;> simp)

theorem normal_degree_zero_mul {r : ℕ} {P Q : MvPolynomial (TV n' k) R} (hP : P ∈ NDsub R n' k r 0) (hQ : Q ∈ NDsub R n' k r 0) :
    P * Q ∈ NDsub R n' k r 0 := by
  rw [NDsub, MvPolynomial.mem_restrictSupport_iff] at hP hQ ⊢
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hm)
  have h1 := hP ha
  have h2 := hQ hb
  simp only [Set.mem_setOf_eq, nonpos_iff_eq_zero] at h1 h2 ⊢
  simp [normDeg_add', h1, h2]

theorem normal_degree_zero_pow {r : ℕ} {P : MvPolynomial (TV n' k) R} (hP : P ∈ NDsub R n' k r 0) (n : ℕ) :
    P ^ n ∈ NDsub R n' k r 0 := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact normal_degree_zero_one r
  | succ n ih =>
    rw [pow_succ]
    exact normal_degree_zero_mul ih hP

theorem normal_degree_zero_prod {r : ℕ} {α : Type} (s : Finset α) (f : α → MvPolynomial (TV n' k) R)
    (h : ∀ i ∈ s, f i ∈ NDsub R n' k r 0) : ∏ i ∈ s, f i ∈ NDsub R n' k r 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact normal_degree_zero_one r
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact normal_degree_zero_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem normal_degree_zero_X_abnormal {r : ℕ} (v : TV n' k) (hv : ¬ IsNormal r v) : (X v : MvPolynomial (TV n' k) R) ∈ NDsub R n' k r 0 := by
  rw [NDsub, MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hm' : m ∈ ({Finsupp.single v 1} : Finset (TV n' k →₀ ℕ)) :=
    MvPolynomial.support_monomial_subset (R := R) hm
  rw [Finset.mem_singleton] at hm'
  subst hm'
  show normDeg r (Finsupp.single v 1) ≤ 0
  unfold normDeg
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, if_neg hv]

theorem normal_degree_zero_det_pmat {r : ℕ} (hrk : r ≤ k) (A : Fin r → Fin n') (P : Fin r → ℕ) (hA : ∀ l, Even (A l).val) :
    (pmat R hrk A P).det ∈ NDsub R n' k r 0 := by
  rw [Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  refine normal_degree_zero_prod _ _ fun i _ => ?_
  refine normal_degree_zero_pow ?_ _
  refine normal_degree_zero_X_abnormal _ ?_
  intro hN
  unfold IsNormal at hN
  rw [if_pos (hA _)] at hN
  simp only [Fin.coe_castLE] at hN
  omega

theorem fixed_symbol_normal_degree_zero (p : ℕ) [NeZero n'] {r : ℕ} (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (hn : Even n')
    (hr : 1 ≤ r) (hrk : r ≤ k) (c' Q : ℕ) : SPR R p F hrk c' Q ∈ NDsub R n' k r 0 := by
  have h1 : ∀ j : ℤ, (pmat R hrk (fun l => posOf n' (F.fr j l.val))
      (fun l => p ^ (zF F j - F.fr j l.val).toNat)).det ∈ NDsub R n' k r 0 := fun j =>
    normal_degree_zero_det_pmat hrk _ _ fun l => (posOf_even hn _).2 (hV.2.2.2.2.1 j l.val l.isLt).2
  have h2 : ∀ s : ℤ, (pmat R hrk (fun l => posOf n' (Arow F s l.val))
      (fun l => p ^ (s - Arow F s l.val).toNat)).det ∈ NDsub R n' k r 0 := fun s =>
    normal_degree_zero_det_pmat hrk _ _ fun l => (posOf_even hn _).2 (window_holds_even_tops n' r F L₁ N₁ hV hn hr s l.val l.isLt).1
  unfold SPR
  exact normal_degree_zero_mul (normal_degree_zero_mul (normal_degree_zero_pow (normal_degree_zero_prod _ _ fun j _ => normal_degree_zero_pow (h1 _) _) _)
    (normal_degree_zero_prod _ _ fun j _ => normal_degree_zero_pow (h1 _) _)) (normal_degree_zero_prod _ _ fun s _ => normal_degree_zero_pow (h2 _) _)

theorem nd_map {R' : Type} [CommRing R'] (f : R →+* R') {r T : ℕ} {P : MvPolynomial (TV n' k) R}
    (hP : P ∈ NDsub R n' k r T) : map f P ∈ NDsub R' n' k r T := by
  rw [NDsub, MvPolynomial.mem_restrictSupport_iff] at hP ⊢
  exact fun m hm => hP (MvPolynomial.support_map_subset f P hm)

theorem nd_rename {r K : ℕ} (hk : k = r + K) {T : ℕ} {P : MvPolynomial (Fin n' × Fin (r + K)) R}
    (hP : ∀ mm ∈ P.support, vsDeg mm ≤ T) : rename (castVK (n' := n') hk) P ∈ NDsub R n' k r T := by
  classical
  rw [NDsub, MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hinj : Function.Injective (castVK (n' := n') hk) := by
    intro x y hxy
    simp only [castVK, Prod.mk.injEq] at hxy
    exact Prod.ext hxy.1 (Fin.cast_injective _ hxy.2)
  rw [Finset.mem_coe, MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨mm, hmm, rfl⟩ := hm
  have key : normDeg r (Finsupp.mapDomain (castVK hk) mm) = vsDeg mm := by
    unfold normDeg vsDeg
    rw [show (∑ v ∈ (Finsupp.mapDomain (castVK hk) mm).support,
        if IsNormal r v then (Finsupp.mapDomain (castVK hk) mm) v else 0) =
        (Finsupp.mapDomain (castVK hk) mm).sum (fun v c => if IsNormal r v then c else 0) from rfl]
    rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by split_ifs <;> simp),
      Finsupp.sum_fintype _ _ (fun _ => by simp), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Fin.sum_univ_add]
    by_cases ht : Even t.val
    · rw [if_pos ht]
      simp [IsNormal, castVK, ht]
    · rw [if_neg ht]
      simp [IsNormal, castVK, ht]
  rw [Set.mem_setOf_eq, key]
  exact hP mm hmm

end Zero

section Sub

variable (p n' : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF p n') O] (w : O) (r : ℕ) {k : ℕ}
  (g : Matrix (Fin k) (Fin k) (WF p n'))

def Nsub (s : Fin n') : Matrix (Fin k) (Fin k) (KK O) := fun a b =>
  if Even s.val then (if r ≤ b.val then algebraMap O (KK O) w else 1) * (sigMat p n' O g (s.val : ℤ))⁻¹ b a
  else (if b.val < r then algebraMap O (KK O) w else 1) * sigMat p n' O g (s.val : ℤ) a b

def NsubInv (s : Fin n') : Matrix (Fin k) (Fin k) (KK O) := fun b c =>
  if Even s.val then (if r ≤ b.val then (algebraMap O (KK O) w)⁻¹ else 1) * sigMat p n' O g (s.val : ℤ) c b
  else (if b.val < r then (algebraMap O (KK O) w)⁻¹ else 1) * (sigMat p n' O g (s.val : ℤ))⁻¹ b c

theorem subst_eq_Lin (f : MvPolynomial (TV n' k) (KK O)) :
    subst p n' O w n' r g f = Lin (Nsub p n' O w r g) f := by
  have key : subst p n' O w n' r g = Lin (Nsub p n' O w r g) := by
    apply MvPolynomial.algHom_ext
    intro v
    unfold subst liftSubst Lin
    rw [aeval_X, aeval_X]
    by_cases hs : Even v.1.val
    · simp only [LLT, hs, decide_true, if_true, Nsub]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs
      · rw [C_mul]; ring
      · rw [one_mul]; ring
    · simp only [LLT, hs, decide_false, Bool.false_eq_true, if_false, Nsub]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs
      · rw [C_mul]; ring
      · rw [one_mul]; ring
  rw [key]

variable {g}

theorem Nsub_mul (hw : algebraMap O (KK O) w ≠ 0) (hg : IsGLW g) (s : Fin n') :
    Nsub p n' O w r g s * NsubInv p n' O w r g s = 1 := by
  ext a c
  simp only [Matrix.mul_apply, Nsub, NsubInv, Matrix.one_apply]
  set σ := sigMat p n' O g (s.val : ℤ) with hσdef
  have hσ : IsUnit σ.det := by
    let φ : WF p n' →+* KK O := (algebraMap O (KK O)).comp ((algebraMap (WF p n') O).comp (sigPow p n' (s.val : ℤ)))
    have h1 : σ = φ.mapMatrix g := by
      ext i j
      rfl
    rw [h1, ← RingHom.map_det]
    exact hg.map φ
  by_cases hs : Even s.val
  · simp only [if_pos hs]
    have h2 : ∀ b : Fin k, (if r ≤ b.val then algebraMap O (KK O) w else 1) * σ⁻¹ b a *
        ((if r ≤ b.val then (algebraMap O (KK O) w)⁻¹ else 1) * σ c b) = σ c b * σ⁻¹ b a := by
      intro b
      split_ifs
      · field_simp
      · ring
    simp_rw [h2]
    rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hσ, Matrix.one_apply]
    simp [eq_comm]
  · simp only [if_neg hs]
    have h2 : ∀ b : Fin k, (if b.val < r then algebraMap O (KK O) w else 1) * σ a b *
        ((if b.val < r then (algebraMap O (KK O) w)⁻¹ else 1) * σ⁻¹ b c) = σ a b * σ⁻¹ b c := by
      intro b
      split_ifs
      · field_simp
      · ring
    simp_rw [h2]
    rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hσ, Matrix.one_apply]

end Sub

end Formalism.MainNotions.TestSideCounting
end
end

