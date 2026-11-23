module

public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvLoc
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

namespace LvLoc


open Classical in
def evKD (W : LocWach PD LL O v n) (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] :
    KsW W s ⊗[LL] D ≃ₗ[LL] (Rs LL PD.p s → D) :=
  (TensorProduct.comm LL (KsW W s) D).trans (TensorProduct.piScalarRight LL LL D (Rs LL PD.p s))

theorem evKD_toKsD (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] (F : Rs LL PD.p s → D) :
    evKD W s D (toKsD W s D F) = F := by
  classical
  show TensorProduct.piScalarRight LL LL D _ (TensorProduct.comm LL (KsW W s) D
    (TensorProduct.comm LL D (KsW W s) ((TensorProduct.piScalarRight LL LL D _).symm F))) = F
  rw [← TensorProduct.comm_symm LL (KsW W s) D, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem evKD_tD (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] (b : (ZMod (PD.p ^ (s + 1)))ˣ)
    (z : KsW W s ⊗[LL] D) (ξ : Rs LL PD.p s) :
    evKD W s D (tD D (precomp LL PD.p s b) z) ξ = evKD W s D z (powR LL PD.p s b ξ) := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f d =>
    simp [evKD, tD, LinearMap.rTensor_tmul, TensorProduct.piScalarRightHom_tmul, precomp_apply]
  | add z z' hz hz' => rw [map_add (f := _), map_add (f := _), Pi.add_apply, hz, hz', map_add (f := _), Pi.add_apply]

theorem tD_toKsD (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] (b : (ZMod (PD.p ^ (s + 1)))ˣ)
    (F : Rs LL PD.p s → D) :
    tD D (precomp LL PD.p s b) (toKsD W s D F) = toKsD W s D (fun ξ => F (powR LL PD.p s b ξ)) := by
  apply (evKD W s D).injective
  funext ξ
  rw [evKD_tD, evKD_toKsD, evKD_toKsD]

theorem dvd_sub_val (s : ℕ) (ω : ℤ_[PD.p]ˣ) :
    (PD.p : ℤ_[PD.p]) ^ (s + 1) ∣ (ω : ℤ_[PD.p]) - ((redU PD.p s ω : ZMod (PD.p ^ (s + 1))).val : ℤ_[PD.p]) := by
  have : NeZero (PD.p ^ (s + 1)) := ⟨(pos_pow PD.p s).ne'⟩
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
    ZMod.natCast_zmod_val, sub_eq_zero]
  rfl

variable {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O} {T : LocLat G Qp LL O} {c : ZMod n}

theorem expN_inv (Lb : LevB W) (hT : IsCrys PD T.ρ)
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (hω : ∀ ω : DeltaT PD.p, ∃ g ∈ W.DelF,
      algebraMap O LL (W.χΓ g : O) = algebraMap O LL (ιZ ((ω.1 : ℤ_[PD.p]ˣ) : ℤ_[PD.p])))
    (hv : ∀ (s : ℕ) (z : ℤ_[PD.p]), (PD.p : ℤ_[PD.p]) ^ (s + 1) ∣ z →
      ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (ιZ z)))
    (s : ℕ) (y : ↥(W.N T)) (hy : ∀ δ ∈ W.DelF, W.γD T δ (y : W.DD T) = y) :
    (levW W uZ ιZ s).Inv (D := Dc W T c) (expN Lb s T c y) := by
  intro j
  obtain ⟨g, hgD, hgχ⟩ := hω j
  apply HahnModule.ext
  funext k
  show ((((levW W uZ ιZ s).a j) ^ k : LLˣ) : LL) •
      tD (Dc W T c) (precomp LL PD.p s (redU PD.p s j.1)) (coefN Lb s T c y k) = coefN Lb s T c y k
  simp only [coefN]
  rw [tD_toKsD, ← map_smul]
  congr 1
  funext ζ
  apply Subtype.ext
  have hx : W.γD T g (y : W.DD T) ∈ W.N T := by rw [hy g hgD]; exact y.2
  have hprim : IsPrimitiveRoot (ζ : LL) (PD.p ^ (s + 1)) := (mem_primitiveRoots (pos_pow PD.p s)).1 ζ.2
  have hval : ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) -
      (((redU PD.p s j.1 : ZMod (PD.p ^ (s + 1))).val : ℕ) : LL)) := by
    rw [hgχ, ← map_natCast (algebraMap O LL), ← map_natCast ιZ, ← map_sub, ← map_sub]
    exact hv s _ (dvd_sub_val s j.1)
  have key := levB_Γ T hT g c ζ _ (s + 1) _ hprim hval rfl y hx k
  have hyy : (⟨W.γD T g (y : W.DD T), hx⟩ : ↥(W.N T)) = y := Subtype.ext (hy g hgD)
  rw [hyy, hgχ] at key
  rw [Pi.smul_apply, SetLike.val_smul]
  show _ • Lb.levB T c (powR LL PD.p s (redU PD.p s j.1) ζ : LL) y k = Lb.levB T c ζ y k
  rw [key, Units.val_zpow_eq_zpow_val]
  rfl

end LvLoc

open LvLoc

variable {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O} {T : LocLat G Qp LL O} {c : ZMod n}

theorem locInv_holds (Lb : LevB W) (C : Coord W (baseIdOf hR) T) (κ : PowerSeries O)
    (hΔ : DeltaRho hR uZ ιZ c) (hT : IsCrys PD T.ρ)
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (hω : ∀ ω : DeltaT PD.p, ∃ g ∈ W.DelF,
      algebraMap O LL (W.χΓ g : O) = algebraMap O LL (ιZ ((ω.1 : ℤ_[PD.p]ˣ) : ℤ_[PD.p])))
    (hv : ∀ (s : ℕ) (z : ℤ_[PD.p]), (PD.p : ℤ_[PD.p]) ^ (s + 1) ∣ z →
      ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (ιZ z))) :
    LocInv Lb C c uZ ιZ κ := by
  intro s x hx j
  have he := expN_inv (c := c) (uZ := uZ) Lb hT levB_Γ hω hv s ⟨C.t c x, hx⟩ fun δ hδ => C.t_Δ c x δ hδ
  have hz := hΔ s j κ
  show Level.δ (levW W uZ ιZ s) j
      (Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ)) • expN Lb s T c ⟨C.t c x, hx⟩) =
    Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ)) • expN Lb s T c ⟨C.t c x, hx⟩
  by_cases hu : IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ))
  · obtain ⟨u, hu⟩ := hu
    rw [← hu] at hz ⊢
    rw [Ring.inverse_unit]
    have h1 : (u : HahnSeries ℤ (KsW W s)) • Level.δ (levW W uZ ιZ s) j
        (((u⁻¹ : (HahnSeries ℤ (KsW W s))ˣ) : HahnSeries ℤ (KsW W s)) • expN Lb s T c ⟨C.t c x, hx⟩) =
        expN Lb s T c ⟨C.t c x, hx⟩ := by
      conv_lhs => rw [← hz]
      rw [Level.δ, ← graded_semilinear_holds, smul_smul, Units.mul_inv, one_smul]
      exact he j
    calc Level.δ (levW W uZ ιZ s) j
          (((u⁻¹ : (HahnSeries ℤ (KsW W s))ˣ) : HahnSeries ℤ (KsW W s)) • expN Lb s T c ⟨C.t c x, hx⟩) =
        ((u⁻¹ : (HahnSeries ℤ (KsW W s))ˣ) : HahnSeries ℤ (KsW W s)) • ((u : HahnSeries ℤ (KsW W s)) •
          Level.δ (levW W uZ ιZ s) j
          (((u⁻¹ : (HahnSeries ℤ (KsW W s))ˣ) : HahnSeries ℤ (KsW W s)) • expN Lb s T c ⟨C.t c x, hx⟩)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [h1]
  · rw [Ring.inverse_non_unit _ hu, zero_smul]
    exact map_zero _

namespace LvLoc

theorem phiIt_mem {O : Type} [CommRing O] {Bs : Formalism.ExponentWindows.E.Base O} {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (PowerSeries O) V] (L : Formalism.ExponentWindows.E.Lat Bs n V) (m : ℕ) (hP : ∀ i, L.P5M i m) (i : ZMod n) :
    ∀ (k : ℕ), ∀ v ∈ L.N i, (∏ s ∈ Finset.range k, Bs.p s ^ m) • L.phiIt i k v ∈ L.N (i + (k : ZMod n))
  | 0 => fun v hv => by simpa [Formalism.ExponentWindows.E.Lat.phiIt] using hv
  | k + 1 => fun v hv => by
    have ih := phiIt_mem L m hP i k v hv
    have e1 : i + ((k + 1 : ℕ) : ZMod n) - 1 = i + (k : ZMod n) := by push_cast; ring
    have h := hP (i + ((k + 1 : ℕ) : ZMod n)) _ (by rw [e1]; exact ih)
    rw [L.φ_semi, smul_smul] at h
    have e : (∏ s ∈ Finset.range (k + 1), Bs.p s ^ m) =
        Bs.q ^ m * Bs.φ (∏ s ∈ Finset.range k, Bs.p s ^ m) := by
      rw [Finset.prod_range_succ', map_prod, mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun s _ => ?_
      simp only [map_pow, Formalism.ExponentWindows.E.Base.p, Function.iterate_succ_apply']
    show (∏ s ∈ Finset.range (k + 1), Bs.p s ^ m) • L.φ (i + ((k + 1 : ℕ) : ZMod n)) (L.phiIt i k v) ∈
      L.N (i + ((k + 1 : ℕ) : ZMod n))
    rw [e]
    exact h

theorem latOf_P5M_of_p5_of_le (C : Coord W (baseIdOf hR) T) {M h : ZMod n → ℕ} (hp5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (hs : W.s = 1) (hRA : RingA W) (m : ℕ) (hm : ∀ i, M i ≤ m) (i : ZMod n) : (latOf C).P5M i m := by
  intro x hx
  show C.t i ((baseIdOf hR).Bs.q ^ m • (latOf C).φ i x) ∈ W.N T
  rw [C.t_smul, map_pow, BaseId.d_q]
  have h1 : C.t i ((latOf C).φ i x) = W.φD T (C.t (i - 1) x) := by
    show (((C.θ i) ((C.θ i).symm (φl W T i (C.θ (i - 1) x))) : ↥(DDl W T i)) : W.DD T) = _
    rw [AddEquiv.apply_symm_apply]
    rfl
  rw [h1]
  have h2 : C.t (i - 1) x ∈ W.Nl T (i - 1) := Submodule.mem_map.2 ⟨_, hx, C.t_letter (i - 1) x⟩
  have h4 := qP_pow_mem hs hRA (W.N T) (hp5.1 i _ h2)
  have e : qP W ^ m = qP W ^ (m - M i) * qP W ^ M i := by rw [← pow_add, Nat.sub_add_cancel (hm i)]
  rw [e, mul_smul]
  exact (W.N T).smul_mem _ h4

end LvLoc

theorem kap_holds (C : Coord W (baseIdOf hR) T) (ell : ℕ) (Λ κ : PowerSeries O) {M h : ZMod n → ℕ}
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hT : IsCrys PD T.ρ) (hJ : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h)
    (hs : W.s = 1) (hRA : RingA W) (m : ℕ) (hm : ∀ i, M i ≤ m)
    (hκ : κ = Λ * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m) :
    ∀ w ∈ (latOf C).W c ell Λ, κ • w ∈ (latOf C).N c := by
  intro w hw
  have hL : ∀ i, (latOf C).P5M i m := latOf_P5M_of_p5_of_le C (hP5 T M h hT hJ) hs hRA m hm
  rw [hκ, mul_comm, mul_smul]
  have hw' : Λ • w ∈ (latOf C).pull (c - (ell : ZMod n)) ell := hw
  have hc : c - (ell : ZMod n) + (ell : ZMod n) = c := sub_add_cancel _ _
  refine Submodule.span_induction (p := fun y _ =>
    (∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m) • y ∈ (latOf C).N c) ?_ ?_ ?_ ?_ hw'
  · rintro _ ⟨u, hu, rfl⟩
    have := phiIt_mem (latOf C) m hL (c - (ell : ZMod n)) ell u hu
    rwa [hc] at this
  · rw [smul_zero]
    exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    rw [smul_add]
    exact Submodule.add_mem _ hy hz
  · intro a y _ hy
    rw [smul_smul, mul_comm, ← smul_smul]
    exact Submodule.smul_mem _ a hy

end Formalism.MainNotions.N.Ln03.Pf
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfMapHyp
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

section General

variable {LL Ks D₁ D₂ : Type} [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D₁]
  [Module LL D₁] [AddCommGroup D₂] [Module LL D₂]

theorem Pf_MapHyp_ambMap_coeff (g : Ks ⊗[LL] D₁ →ₗ[Ks] Ks ⊗[LL] D₂) (f : Amb LL Ks D₁) (k : ℤ) :
    ((HahnModule.of Ks).symm (ambMap g f)).coeff k = g (((HahnModule.of Ks).symm f).coeff k) :=
  rfl

theorem Pf_MapHyp_ambMap_smul (g : Ks ⊗[LL] D₁ →ₗ[Ks] Ks ⊗[LL] D₂) (x : HahnSeries ℤ Ks)
    (f : Amb LL Ks D₁) : ambMap g (x • f) = x • ambMap g f := by
  have hsupp : ((HahnModule.of Ks).symm (ambMap g f)).support ⊆
      ((HahnModule.of Ks).symm f).support := by
    intro k hk
    rw [HahnSeries.mem_support] at hk ⊢
    intro h0
    apply hk
    rw [Pf_MapHyp_ambMap_coeff, h0, map_zero]
  apply HahnModule.ext
  funext k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [HahnModule.coeff_smul_right (y := ambMap g f) ((HahnModule.of Ks).symm f).isPWO_support hsupp,
    Pf_MapHyp_ambMap_coeff, HahnModule.coeff_smul, map_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [map_smul, Pf_MapHyp_ambMap_coeff]

theorem Pf_MapHyp_baseChange_tD (h : D₁ →ₗ[LL] D₂) (τ : Ks ≃ₐ[LL] Ks) (a : LL) (y : Ks ⊗[LL] D₁) :
    h.baseChange Ks (a • tD D₁ τ y) = a • tD D₂ τ (h.baseChange Ks y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x d => simp [tD, LinearMap.baseChange_tmul, TensorProduct.smul_tmul']
  | add y y' hy hy' => simp only [map_add (f := _), smul_add, hy, hy']

theorem Pf_MapHyp_grd_ambMap (h : D₁ →ₗ[LL] D₂) (τ : Ks ≃ₐ[LL] Ks) (a : LLˣ) (f : Amb LL Ks D₁) :
    grd (D := D₂) τ a (ambMap (h.baseChange Ks) f) = ambMap (h.baseChange Ks) (grd (D := D₁) τ a f) := by
  apply HahnModule.ext
  funext i
  change ((a ^ i : LLˣ) : LL) • tD D₂ τ (h.baseChange Ks (cf f i)) =
    h.baseChange Ks (((a ^ i : LLˣ) : LL) • tD D₁ τ (cf f i))
  rw [Pf_MapHyp_baseChange_tD]

end General

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

variable {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

variable {W : LocWach PD LL O v n} {T₁ T₂ : LocLat G Qp LL O}
variable {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O} {c : ZMod n}

theorem memD_holds (W : LocWach PD LL O v n) (F : LatHom T₁.L T₂.L) (c : ZMod n) : MemD W F c := by
  intro x hx
  have hA : ∀ (g : G) (y : T₁.V ⊗[Qp] B),
      AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) (actVB PD T₁.ρ g y) =
        actVB PD T₂.ρ g (AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul w b => simp [actVB, AlgebraTensorModule.map_tmul, F.equiv]
    | add y y' hy hy' => simp only [map_add (f := _), hy, hy']
  have hB : ∀ (c' : K₀) (y : T₁.V ⊗[Qp] B),
      AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B)
          (mulVB (K₀ := K₀) (B := B) (V := T₁.V) (LL := LL) c' y) =
        mulVB (K₀ := K₀) (B := B) (V := T₂.V) (LL := LL) c'
          (AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) y) := by
    intro c' y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul w b => simp [mulVB, AlgebraTensorModule.map_tmul]
    | add y y' hy hy' => simp only [map_add (f := _), hy, hy']
  simp only [DcrisL, Dcris, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero] at hx ⊢
  exact ⟨fun g => by rw [← hA, hx.1 g], fun c' => by rw [← hB, hx.2 c', map_smul]⟩

theorem smul_holds {F : LatHom T₁.L T₂.L} (memD : MemD W F c) :
    ∀ (s : ℕ) (x : HahnSeries ℤ (KsW W s)) (f : Amb LL (KsW W s) (Dc W T₁ c)),
      ambF memD s (x • f) = x • ambF memD s f :=
  fun s x f => Pf_MapHyp_ambMap_smul ((dmapOf memD).baseChange (KsW W s)) x f

theorem inv_holds {F : LatHom T₁.L T₂.L} (memD : MemD W F c) :
    ∀ (s : ℕ) (f : Amb LL (KsW W s) (Dc W T₁ c)), (levW W uZ ιZ s).Inv f →
      (levW W uZ ιZ s).Inv (ambF memD s f) := by
  intro s f hf j
  have hj : (levW W uZ ιZ s).δ j f = f := hf j
  show (levW W uZ ιZ s).δ j (ambF memD s f) = ambF memD s f
  rw [Level.δ] at hj ⊢
  unfold ambF
  rw [Pf_MapHyp_grd_ambMap, hj]

theorem mapHyp_holds (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (F : LatHom T₁.L T₂.L)
    (c : ZMod n) : MapHyp hR uZ ιZ F c :=
  ⟨memD_holds W F c, smul_holds (memD_holds W F c), inv_holds (memD_holds W F c)⟩

end Formalism.MainNotions.N.Ln03.Pf
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PrimitiveRootPowPrime
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

theorem convolution_one {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (g : ℤ → M) (k : ℤ) :
    ConvolutionAlt.cv (1 : PowerSeries R) g k = g k := by
  unfold ConvolutionAlt.cv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [PowerSeries.coeff_one, if_neg hj, zero_smul]

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

variable {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

def phiIt (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (m : ℕ) (x : W.DD T) : ℕ → W.DD T
  | 0 => x
  | i + 1 => W.Q ^ m • W.φD T (phiIt W T m x i)

variable {W : LocWach PD LL O v n}

theorem primitive_root_pow_prime {ζ : LL} (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    ∃ j : ℕ, IsPrimitiveRoot (ζ ^ PD.p) (PD.p ^ j) := by
  obtain ⟨j, hj⟩ := hζ
  rcases j with _ | j
  · refine ⟨0, ?_⟩
    rw [pow_zero, IsPrimitiveRoot.one_right_iff] at hj ⊢
    rw [hj, one_pow]
  · refine ⟨j, hj.pow (pow_pos (Fact.out : PD.p.Prime).pos _) ?_⟩
    rw [pow_succ']

theorem phiIt_levB_gen (Lb : LevB W) (T : LocLat G Qp LL O)
    (levB_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
      (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
          (((PD.p : LL) ^ (k - (j : ℤ))) •
            φVB PD (LL := LL) (V := T.V) (Lb.levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ)))))
    (lev_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))
    (hp0 : (PD.p : LL) ≠ 0)
    (m : ℕ) (a : ZMod n) (x : W.DD T) :
    ∀ (i : ℕ) (hN : ∀ r ≤ i, phiIt W T m x r ∈ W.N T) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) →
      ∀ k : ℤ, Lb.levB T (a + i) ζ ⟨phiIt W T m x i, hN i le_rfl⟩ k =
        ConvolutionAlt.cv (W.lev (a + i) ζ (∏ r ∈ Finset.range i, W.φA^[r] (W.Q ^ m)))
          (fun k => ((PD.p : LL) ^ ((i : ℤ) * k)) • (φVB PD (LL := LL) (V := T.V))^[i]
            (Lb.levB T a (ζ ^ PD.p ^ i) ⟨x, hN 0 (Nat.zero_le _)⟩ k)) k := by
  intro i
  induction i with
  | zero =>
    intro hN ζ _ k
    rw [Finset.prod_range_zero, map_one, convolution_one]
    simp only [Nat.cast_zero, add_zero, zero_mul, zpow_zero, one_smul, Function.iterate_zero, id, pow_zero,
      pow_one]
    rfl
  | succ i ih =>
    intro hN ζ hζ k
    have hNi : ∀ r ≤ i, phiIt W T m x r ∈ W.N T := fun r hr => hN r (Nat.le_succ_of_le hr)
    have hζp := primitive_root_pow_prime (PD := PD) hζ
    have hstep := levB_φ (a + ((i + 1 : ℕ) : ZMod n)) ζ hζ ⟨phiIt W T m x i, hNi i le_rfl⟩ m (hN (i + 1) le_rfl) k
    have hlet : a + ((i + 1 : ℕ) : ZMod n) - 1 = a + (i : ZMod n) := by push_cast; ring
    rw [hlet] at hstep
    have e0 : (⟨phiIt W T m x (i + 1), hN (i + 1) le_rfl⟩ : ↥(W.N T)) =
        ⟨W.Q ^ m • W.φD T ((⟨phiIt W T m x i, hNi i le_rfl⟩ : ↥(W.N T)) : W.DD T), hN (i + 1) le_rfl⟩ := rfl
    rw [e0, hstep]
    set L := W.lev (a + ((i + 1 : ℕ) : ZMod n)) ζ (W.Q ^ m) with hL
    set F := W.lev (a + (i : ZMod n)) (ζ ^ PD.p) (∏ r ∈ Finset.range i, W.φA^[r] (W.Q ^ m)) with hF
    set φ := φVB PD (LL := LL) (V := T.V) with hφ
    set g0 : ℤ → T.V ⊗[Qp] B := fun k => Lb.levB T a ((ζ ^ PD.p) ^ PD.p ^ i) ⟨x, hN 0 (Nat.zero_le _)⟩ k
      with hg0
    set h : ℤ → T.V ⊗[Qp] B := fun k => ((PD.p : LL) ^ ((i : ℤ) * k)) • φ^[i] (g0 k) with hh
    obtain ⟨m0, hm0⟩ := Lb.supp T a ((ζ ^ PD.p) ^ PD.p ^ i) ⟨x, hN 0 (Nat.zero_le _)⟩
    have hh0 : ∀ k < m0, h k = 0 := fun k hk => by
      simp only [hh, hg0, hm0 k hk, Function.iterate_fixed (map_zero φ) i, smul_zero]
    have hh1 : ∀ k < m0, (fun k => (PD.p : LL) ^ k • φ (h k)) k = 0 := fun k hk => by
      simp only [hh0 k hk, map_zero, smul_zero]
    have hfun : (fun k => (PD.p : LL) ^ k • φ (Lb.levB T (a + (i : ZMod n)) (ζ ^ PD.p)
        ⟨phiIt W T m x i, hNi i le_rfl⟩ k)) = fun k => ConvolutionAlt.cv (PowerSeries.rescale (PD.p : LL) F)
          (fun k => (PD.p : LL) ^ k • φ (h k)) k := by
      funext k'
      rw [ih hNi (ζ ^ PD.p) hζp k']
      exact ConvolutionAlt.cv_twist φ (PD.p : LL) hp0 F h m0 hh0 k'
    show ConvolutionAlt.cv L (fun k => (PD.p : LL) ^ k • φ (Lb.levB T (a + (i : ZMod n)) (ζ ^ PD.p)
        ⟨phiIt W T m x i, hNi i le_rfl⟩ k)) k = _
    rw [hfun, ← ConvolutionAlt.cv_mul L (PowerSeries.rescale (PD.p : LL) F) _ m0 hh1 k]
    have hser : L * PowerSeries.rescale (PD.p : LL) F =
        W.lev (a + ((i + 1 : ℕ) : ZMod n)) ζ (∏ r ∈ Finset.range (i + 1), W.φA^[r] (W.Q ^ m)) := by
      rw [hF, ← hlet, ← lev_φ _ ζ hζ, hL, ← map_mul, Finset.prod_range_succ', map_prod]
      congr 1
      rw [mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [Function.iterate_succ_apply']
    have hfn : (fun k => (PD.p : LL) ^ k • φ (h k)) = fun k => ((PD.p : LL) ^ (((i + 1 : ℕ) : ℤ) * k)) •
        φ^[i + 1] (Lb.levB T a (ζ ^ PD.p ^ (i + 1)) ⟨x, hN 0 (Nat.zero_le _)⟩ k) := by
      funext k'
      simp only [hh, hg0]
      rw [map_smul, smul_smul, ← zpow_add₀ hp0, Function.iterate_succ_apply', ← pow_mul, ← pow_succ']
      congr 2
      push_cast; ring
    rw [hser, hfn]

theorem phiIt_levB (Lb : LevB W) (T : LocLat G Qp LL O)
    (levB_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
      (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
          (((PD.p : LL) ^ (k - (j : ℤ))) •
            φVB PD (LL := LL) (V := T.V) (Lb.levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ)))))
    (lev_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))
    (hp0 : (PD.p : LL) ≠ 0)
    (m : ℕ) (c : ZMod n) (ell : ℕ) (x : W.DD T) (hN : ∀ i ≤ ell, phiIt W T m x i ∈ W.N T)
    (s : ℕ) (hs : s < ell) (ζ : LL) (hζ : IsPrimitiveRoot ζ (PD.p ^ (s + 1))) (k : ℤ) :
    Lb.levB T c ζ ⟨phiIt W T m x ell, hN ell le_rfl⟩ k =
      ConvolutionAlt.cv (W.lev c ζ (∏ i ∈ Finset.range ell, W.φA^[i] (W.Q ^ m)))
        (fun k => ((PD.p : LL) ^ ((ell : ℤ) * k)) • (φVB PD (LL := LL) (V := T.V))^[ell]
          (Lb.levB T (c - ell) 1 ⟨x, hN 0 (Nat.zero_le _)⟩ k)) k := by
  have h := phiIt_levB_gen Lb T levB_φ lev_φ hp0 m (c - ell) x ell hN ζ ⟨s + 1, hζ⟩ k
  have h1 : ζ ^ PD.p ^ ell = 1 :=
    (hζ.pow_eq_one_iff_dvd _).2 (pow_dvd_pow _ hs)
  rw [h1, sub_add_cancel] at h
  exact h

end Formalism.MainNotions.N.Ln03.Pf
end
end

