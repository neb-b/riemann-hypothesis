module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0027
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfMapLocL
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

section Cst

variable {LL Ks D D₂ : Type} [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
  [AddCommGroup D₂] [Module LL D₂]

theorem mapLocL_cstD_add (d d' : D) :
    cstD (LL := LL) Ks (d + d') = cstD Ks d + cstD Ks d' := by
  simp [cstD, TensorProduct.tmul_add]

theorem mapLocL_cstD_zero : cstD (LL := LL) (D := D) Ks 0 = 0 := by
  simp [cstD]

theorem mapLocL_cstD_sum {ι : Type} (s : Finset ι) (f : ι → D) :
    cstD (LL := LL) Ks (∑ i ∈ s, f i) = ∑ i ∈ s, cstD Ks (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mapLocL_cstD_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mapLocL_cstD_add, ih]

theorem mapLocL_C_smul_cstD (x : LL) (d : D) :
    (HahnSeries.C (algebraMap LL Ks x) : HahnSeries ℤ Ks) • cstD (LL := LL) Ks d = cstD Ks (x • d) := by
  apply HahnModule.ext
  funext i
  rw [HahnSeries.C_apply, HahnModule.coeff_single_zero_smul]
  simp only [cstD, Equiv.symm_apply_apply, HahnSeries.coeff_single]
  split_ifs
  · rw [TensorProduct.tmul_smul, algebraMap_smul]
  · rw [smul_zero]

theorem mapLocL_ambMap_cstD (g : Ks ⊗[LL] D →ₗ[Ks] Ks ⊗[LL] D₂) (d : D) :
    ambMap g (cstD (LL := LL) Ks d) = HahnModule.of Ks (HahnSeries.single 0 (g ((1 : Ks) ⊗ₜ[LL] d))) := by
  apply HahnModule.ext
  funext i
  simp only [ambMap, cstD, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Equiv.symm_apply_apply]
  rw [HahnSeries.map_coeff]
  simp only [HahnSeries.coeff_single]
  split_ifs <;> simp

end Cst

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

section Helpers

theorem mapLocL_ambF_cstD {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {c : ZMod n}
    (h : MemD W F c) (s : ℕ) (d : Dc W T₁ c) :
    ambF h s (cstD (KsW W s) d) = cstD (KsW W s) (dmapOf h d) := by
  unfold ambF
  rw [mapLocL_ambMap_cstD, LinearMap.baseChange_tmul]
  rfl

theorem mapLocL_cmp_d (hR : Ring9 W) (T : LocLat G Qp LL O) (a : PowerSeries O) (x : ↥(W.N T)) :
    W.cmp T ((baseIdOf hR).d a • x) = algebraMap O LL (PowerSeries.constantCoeff a) • W.cmp T x := by
  set a' : PowerSeries O := PowerSeries.mk fun p => PowerSeries.coeff (p + 1) a
  set π' : PowerSeries O := PowerSeries.mk fun p => PowerSeries.coeff (p + 1) W.π₀₁
  have ha : a = PowerSeries.X * a' + PowerSeries.C (PowerSeries.constantCoeff a) :=
    PowerSeries.eq_X_mul_shift_add_const a
  have hπ : W.π₀₁ = PowerSeries.X * π' := by
    have := PowerSeries.eq_X_mul_shift_add_const W.π₀₁
    rwa [π₀₁_const hR, map_zero, add_zero] at this
  have hd : (baseIdOf hR).d a = (letπ : LetA O n) * ((fun _ => π') * (baseIdOf hR).d a') +
      algebraMap O (LetA O n) (PowerSeries.constantCoeff a) := by
    funext i
    have hC0 : (PowerSeries.C (PowerSeries.constantCoeff a) : PowerSeries O) =
        algebraMap O (PowerSeries O) (PowerSeries.constantCoeff a) := by
      rw [PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [BaseId.d_apply]
    conv_lhs => rw [ha, hC0, map_add (f := _), map_mul, AlgHom.commutes, (baseIdOf hR).ι_X, hπ]
    simp only [Pi.add_apply, Pi.mul_apply, BaseId.d_apply, letπ, Pi.algebraMap_apply]
    ring
  rw [hd, add_smul, map_add (f := _), mul_smul, W.cmp_π, zero_add, algebraMap_smul, W.cmp_smul]

theorem mapLocL_t_sum {T : LocLat G Qp LL O} (C : Coord W (baseIdOf hR) T) (i : ZMod n) {ι : Type}
    (s : Finset ι) (f : ι → C.V) : C.t i (∑ l ∈ s, f l) = ∑ l ∈ s, C.t i (f l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [C.t_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, C.t_add, ih]

theorem mapLocL_map_φVB {T₁ T₂ : LocLat G Qp LL O} (f : T₁.V →ₗ[LL] T₂.V) (z : T₁.V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (φVB PD (LL := LL) (V := T₁.V) z) =
      φVB PD (LL := LL) (V := T₂.V) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [φVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mapLocL_map_φVB_pow {T₁ T₂ : LocLat G Qp LL O} (f : T₁.V →ₗ[LL] T₂.V) (e : ℕ)
    (z : T₁.V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (((φVB PD (LL := LL) (V := T₁.V)) ^ e) z) =
      ((φVB PD (LL := LL) (V := T₂.V)) ^ e) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) z) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', Module.End.mul_apply, mapLocL_map_φVB, ih, pow_succ', Module.End.mul_apply]

theorem mapLocL_cmp_map {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁}
    {C₂ : Coord W (baseIdOf hR) T₂} {F : LatHom T₁.L T₂.L} (hC : CoordHom C₁ C₂ F) (i : ZMod n)
    {r : ℕ} (x : C₁.V) (hx : C₁.t i x ∈ W.N T₁) (e₂ : Fin r → C₂.V) (he₂ : ∀ l, C₂.t i (e₂ l) ∈ W.N T₂)
    (a : Fin r → PowerSeries O) (ha : hC.f x = ∑ l, a l • e₂ l) :
    AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) (W.cmp T₁ ⟨C₁.t i x, hx⟩) =
      ∑ l, algebraMap O LL (PowerSeries.constantCoeff (a l)) • W.cmp T₂ ⟨C₂.t i (e₂ l), he₂ l⟩ := by
  have hy : W.map F ((⟨C₁.t i x, hx⟩ : ↥(W.N T₁)) : W.DD T₁) ∈ W.N T₂ := by
    show W.map F (C₁.t i x) ∈ W.N T₂
    rw [← hC.coord_hom_map_trace]
    exact (latHomOf hC).map_N i x hx
  rw [← W.cmp_map F hC.crys hC.crys' ⟨C₁.t i x, hx⟩ hy]
  have heq : (⟨W.map F ((⟨C₁.t i x, hx⟩ : ↥(W.N T₁)) : W.DD T₁), hy⟩ : ↥(W.N T₂)) =
      ∑ l, (baseIdOf hR).d (a l) • (⟨C₂.t i (e₂ l), he₂ l⟩ : ↥(W.N T₂)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    show W.map F (C₁.t i x) = ∑ l, (baseIdOf hR).d (a l) • C₂.t i (e₂ l)
    rw [← hC.coord_hom_map_trace, ha, mapLocL_t_sum]
    simp only [Coord.t_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [heq, map_sum]
  simp only [mapLocL_cmp_d]

theorem mapLocL_lamOf_coe {T : LocLat G Qp LL O} (C : Coord W (baseIdOf hR) T) (c : ZMod n) (ell : ℕ)
    {r : ℕ} (e : Fin r → C.V) (k : Fin r) (hk : C.t (c - (ell : ZMod n)) (e k) ∈ W.N T) :
    ((lamOf C c ell e k : Dc W T c) : T.V ⊗[Qp] B) =
      ((φVB PD (LL := LL) (V := T.V)) ^ ell) (W.cmp T ⟨C.t (c - (ell : ZMod n)) (e k), hk⟩) := by
  have h1 : W.cmp T ⟨C.t (c - (ell : ZMod n)) (e k), hk⟩ ∈ DcrisL PD T.ρ (W.emb (c - (ell : ZMod n))) := by
    have h0 := W.cmp_letter T (c - (ell : ZMod n)) ⟨_, hk⟩
    have hx : ((letE (c - (ell : ZMod n)) : LetA O n) • (⟨C.t (c - (ell : ZMod n)) (e k), hk⟩ : ↥(W.N T))) =
        ⟨C.t (c - (ell : ZMod n)) (e k), hk⟩ := Subtype.ext (C.t_letter _ _)
    rwa [hx] at h0
  have h' : ((φVB PD (LL := LL) (V := T.V)) ^ ell) (W.cmp T ⟨C.t (c - (ell : ZMod n)) (e k), hk⟩) ∈
      DcrisL PD T.ρ (W.emb c) := by
    have h2 := Formalism.MainNotions.UnusedSlot80.ArcF.φVB_pow_letter W T (c - (ell : ZMod n)) h1 ell
    rwa [sub_add_cancel] at h2
  unfold lamOf
  rw [dite_eq_left hk, dite_eq_left h']

end Helpers

section ThetaShiftProofs

variable {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁} {C₂ : Coord W (baseIdOf hR) T₂}
  {F : LatHom T₁.L T₂.L} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ} {κ₁ κ₂ : PowerSeries O} {r₁ r₂ : ℕ}
  {lam₁ : Fin r₁ → Dc W T₁ c} {lam₂ : Fin r₂ → Dc W T₂ c}

theorem mapLocL_dmap_lam (hC : CoordHom C₁ C₂ F) (Mh : MapHyp hR uZ ιZ F c)
    (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V) (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (he₁ : ∀ k, e₁ k ∈ (latOf C₁).N (c - (ell : ZMod n)))
    (he₂ : ∀ l, e₂ l ∈ (latOf C₂).N (c - (ell : ZMod n)))
    (hP : ∀ k, ∃ a : Fin r₂ → PowerSeries O, (latHomOf hC).f (e₁ k) = ∑ l, a l • e₂ l ∧
      ∀ l, LinearMap.toMatrix' P l k = PowerSeries.constantCoeff (a l)) (k : Fin r₁) :
    dmapOf Mh.memD (lamOf C₁ c ell e₁ k) =
      ∑ l, algebraMap O LL (LinearMap.toMatrix' P l k) • lamOf C₂ c ell e₂ l := by
  obtain ⟨a, ha, hPa⟩ := hP k
  apply Subtype.ext
  rw [Submodule.coe_sum]
  show AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) ((lamOf C₁ c ell e₁ k : Dc W T₁ c) : T₁.V ⊗[Qp] B) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [mapLocL_lamOf_coe C₁ c ell e₁ k (he₁ k), mapLocL_map_φVB_pow,
    mapLocL_cmp_map hC _ (e₁ k) (he₁ k) e₂ he₂ a ha, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, Submodule.coe_smul, mapLocL_lamOf_coe C₂ c ell e₂ l (he₂ l), hPa l]

theorem loclComm_holds (hC : CoordHom C₁ C₂ F)
    (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₁ lam₁)
    (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₂ lam₂)
    (Mh : MapHyp hR uZ ιZ F c) (j M g η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ)
    (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V) (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (hlam₁ : lam₁ = lamOf C₁ c ell e₁) (hlam₂ : lam₂ = lamOf C₂ c ell e₂)
    (he₁ : ∀ k, e₁ k ∈ (latOf C₁).N (c - (ell : ZMod n)))
    (he₂ : ∀ l, e₂ l ∈ (latOf C₂).N (c - (ell : ZMod n)))
    (hP : ∀ k, ∃ a : Fin r₂ → PowerSeries O, (latHomOf hC).f (e₁ k) = ∑ l, a l • e₂ l ∧
      ∀ l, LinearMap.toMatrix' P l k = PowerSeries.constantCoeff (a l)) :
    ∀ s < ell, ∀ y : Fin r₁ → PowerSeries O,
      prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell
          ((lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).locL s y) =
        (lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).locL s (E.extL P y) := by
  subst hlam₁ hlam₂
  intro s _ y
  apply prL_inj
  intro s' hs'
  erw [prL_of_lt s' hs', prL_of_lt s' hs']
  change ambF Mh.memD s' (locLF (hR := hR) (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) (lamOf C₁ c ell e₁) s' y) =
    locLF (hR := hR) (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) (lamOf C₂ c ell e₂) s' (E.extL P y)
  have hk : ∀ k, ambF Mh.memD s' (cstD (KsW W s') (lamOf C₁ c ell e₁ k)) =
      ∑ l, HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' (PowerSeries.C (LinearMap.toMatrix' P l k))) •
        cstD (KsW W s') (lamOf C₂ c ell e₂ l) := by
    intro k
    rw [mapLocL_ambF_cstD, mapLocL_dmap_lam hC Mh e₁ e₂ P he₁ he₂ hP k, mapLocL_cstD_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Hy₂.rhoC, HahnSeries.ofPowerSeries_C, mapLocL_C_smul_cstD]
  have hext : ∀ l, E.extL P y l = ∑ k, PowerSeries.C (LinearMap.toMatrix' P l k) * y k := by
    intro l
    simp [E.extL, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  simp only [locLF]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Mh.smul, map_sum]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Mh.smul, hk, hext, map_sum, map_mul, Finset.sum_smul, mul_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => smul_comm _ _ _

theorem prLIs_holds (hC : CoordHom C₁ C₂ F) {r₁ r₂ : ℕ}
    (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V) (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (he₂ : ∀ l, e₂ l ∈ (latOf C₂).N (c - (ell : ZMod n)))
    (hP : ∀ k, ∃ a : Fin r₂ → PowerSeries O, (latHomOf hC).f (e₁ k) = ∑ l, a l • e₂ l ∧
      ∀ l, LinearMap.toMatrix' P l k = PowerSeries.constantCoeff (a l)) :
    ∀ k, (latHomOf hC).f (e₁ k) -
      ∑ l, PowerSeries.C (LinearMap.toMatrix' P l k) • e₂ l ∈
    E.sm (PowerSeries.X : PowerSeries O) ((latOf C₂).N (c - (ell : ZMod n))) := by
  intro k
  obtain ⟨a, ha, hPa⟩ := hP k
  refine Submodule.mem_map.2 ⟨∑ l, (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (a l)) • e₂ l,
    Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (he₂ l), ?_⟩
  rw [LinearMap.lsmul_apply, Finset.smul_sum, ha, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul, hPa l, ← sub_smul]
  congr 1
  rw [eq_sub_iff_add_eq]
  exact (PowerSeries.eq_X_mul_shift_add_const (a l)).symm

end ThetaShiftProofs

end Formalism.MainNotions.N.Ln03.Pf
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PowerSeriesCancelBounded
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

section Content

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem C_dvd_iff_dvd_coeffs (ϖ : O) (f : PowerSeries O) :
    PowerSeries.C ϖ ∣ f ↔ ∀ k, ϖ ∣ PowerSeries.coeff k f := by
  constructor
  · rintro ⟨g, rfl⟩ k
    rw [PowerSeries.coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    choose g hg using h
    refine ⟨PowerSeries.mk g, ?_⟩
    ext k
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hg]

theorem prime_C_uniformizer {ϖ : O} (hϖ : Irreducible ϖ) : Prime (PowerSeries.C ϖ : PowerSeries O) := by
  have : (Ideal.span {ϖ} : Ideal O).IsPrime := (Ideal.span_singleton_prime hϖ.ne_zero).2 hϖ.prime
  have key : ∀ f : PowerSeries O, PowerSeries.C ϖ ∣ f ↔
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) f = 0 := by
    intro f
    rw [C_dvd_iff_dvd_coeffs]
    constructor
    · intro h
      ext k
      rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact h k
    · intro h k
      have h1 := congrArg (PowerSeries.coeff k) h
      rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h1
      exact h1
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hϖ.ne_zero
    simpa using congrArg PowerSeries.constantCoeff h
  · intro hu
    apply hϖ.not_isUnit
    simpa using hu.map PowerSeries.constantCoeff
  · intro f g hfg
    rw [key, map_mul] at hfg
    rcases mul_eq_zero.1 hfg with h | h
    · exact Or.inl ((key f).2 h)
    · exact Or.inr ((key g).2 h)

theorem power_series_cancel_bounded (q : O) {f : PowerSeries O} (hf : f ≠ 0) :
    ∃ c₀ : ℕ, ∀ (k : ℕ) (g : PowerSeries O),
      (PowerSeries.C q) ^ (k + c₀) ∣ f * g → (PowerSeries.C q) ^ k ∣ g := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hP := prime_C_uniformizer hϖ
  set P : PowerSeries O := PowerSeries.C ϖ with hPdef
  have hex : ∃ v : ℕ, ¬ P ^ (v + 1) ∣ f := by
    obtain ⟨k, hk⟩ : ∃ k, PowerSeries.coeff k f ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hf (PowerSeries.ext fun k => by simpa using hall k)
    obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hk hϖ
    refine ⟨e, fun hd => ?_⟩
    rw [hPdef, ← map_pow, C_dvd_iff_dvd_coeffs] at hd
    have h1 : ϖ ^ (e + 1) ∣ ϖ ^ e := he.dvd_iff_dvd_right.1 (hd k)
    have h2 := (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h1
    omega
  classical
  set v := Nat.find hex with hv
  have hnot : ¬ P ^ (v + 1) ∣ f := Nat.find_spec hex
  have hdv : P ^ v ∣ f := by
    rcases Nat.eq_zero_or_pos v with h0 | hpos
    · rw [h0, pow_zero]
      exact one_dvd _
    · have h1 := not_not.1 (Nat.find_min hex (show v - 1 < v by omega))
      rwa [show v - 1 + 1 = v by omega] at h1
  obtain ⟨f', hf'⟩ := hdv
  have hf'P : ¬ P ∣ f' := by
    rintro ⟨u, hu⟩
    apply hnot
    exact ⟨u, by rw [hf', hu, pow_succ, mul_assoc]⟩
  have iter : ∀ (M : ℕ) (g : PowerSeries O), P ^ M ∣ f' * g → P ^ M ∣ g := by
    intro M
    induction M with
    | zero => intro g _; rw [pow_zero]; exact one_dvd _
    | succ M ih =>
      intro g hg
      have h1 : P ∣ f' * g := dvd_trans (dvd_pow_self P (Nat.succ_ne_zero M)) hg
      obtain ⟨g', rfl⟩ := (hP.dvd_or_dvd h1).resolve_left hf'P
      have h2 : P ^ M ∣ f' * g' := by
        rw [pow_succ', show f' * (P * g') = P * (f' * g') by ring] at hg
        exact (mul_dvd_mul_iff_left hP.ne_zero).1 hg
      rw [pow_succ']
      exact mul_dvd_mul_left P (ih g' h2)
  refine ⟨v, fun k g hg => ?_⟩
  by_cases hq : q = 0
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk, pow_zero]
      exact one_dvd _
    · rw [hq, map_zero, zero_pow (by omega), zero_dvd_iff] at hg
      rcases mul_eq_zero.1 hg with h | h
      · exact absurd h hf
      · rw [h]
        exact dvd_zero _
  · obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hq hϖ
    have hA : ∀ j : ℕ, Associated ((PowerSeries.C q) ^ j) (P ^ (e * j)) := fun j => by
      have h0 := (he.map PowerSeries.C).pow_pow (n := j)
      rw [map_pow, ← pow_mul] at h0
      exact h0
    rcases Nat.eq_zero_or_pos e with he0 | he0
    · rw [(hA k).dvd_iff_dvd_left, he0, zero_mul, pow_zero]
      exact one_dvd _
    · rw [(hA (k + v)).dvd_iff_dvd_left, hf'] at hg
      have h1 : P ^ v * P ^ (e * k) ∣ P ^ v * (f' * g) := by
        rw [← pow_add, ← mul_assoc]
        exact dvd_trans (pow_dvd_pow P (by nlinarith)) hg
      have h2 := (mul_dvd_mul_iff_left (pow_ne_zero v hP.ne_zero)).1 h1
      rw [(hA k).dvd_iff_dvd_left]
      exact iter _ g h2

end Content

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

theorem isRegular_image_in_EE [IsDomain O] [IsDiscreteValuationRing O] (hR : Ring9 W)
    {κ : PowerSeries O} (hκ : κ ≠ 0) (x : W.EE)
    (hx : algebraMap (LetA O n) W.EE ((baseIdOf hR).d κ) * x = 0) : x = 0 := by
  have := W.EE_complete
  have hf : (baseIdOf hR).ι κ ≠ 0 := fun h => hκ (baseIdOf_inj hR (by rw [h, map_zero]))
  obtain ⟨c₀, hc₀⟩ := power_series_cancel_bounded ((PD.p : ℕ) : O) hf
  have key : ∀ k : ℕ, x ∈ Ideal.span {((PD.p : ℕ) : W.EE) ^ k} := by
    intro k
    obtain ⟨a, m, ham⟩ := W.EE_dense x (k + c₀)
    have h1 : algebraMap (LetA O n) W.EE ((baseIdOf hR).d κ * a) ∈
        Ideal.span {((PD.p : ℕ) : W.EE) ^ (k + c₀)} := by
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 ham
      rw [Ideal.mem_span_singleton']
      refine ⟨-(algebraMap (LetA O n) W.EE ((baseIdOf hR).d κ) * y), ?_⟩
      have e : algebraMap (LetA O n) W.EE a =
          x * algebraMap (LetA O n) W.EE (letπ ^ m) - y * ((PD.p : ℕ) : W.EE) ^ (k + c₀) := by
        rw [hy]; ring
      rw [map_mul, e, mul_sub, ← mul_assoc, hx, zero_mul]
      ring
    obtain ⟨b, hb⟩ := W.EE_sat _ _ h1
    have h2 : ∀ i, (PowerSeries.C ((PD.p : ℕ) : O)) ^ k ∣ a i := by
      intro i
      apply hc₀ k (a i)
      have h3 := congrFun hb i
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, BaseId.d_apply] at h3
      rw [map_natCast, h3]
      exact dvd_mul_right _ _
    choose d hd using h2
    have h4 : algebraMap (LetA O n) W.EE a ∈ Ideal.span {((PD.p : ℕ) : W.EE) ^ k} := by
      have h5 : a = ((PD.p : ℕ) : LetA O n) ^ k * d := by
        funext i
        simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply]
        rw [hd i, map_natCast]
      rw [h5, map_mul, map_pow, map_natCast]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    have ham' : x * algebraMap (LetA O n) W.EE (letπ ^ m) - algebraMap (LetA O n) W.EE a ∈
        Ideal.span {((PD.p : ℕ) : W.EE) ^ k} :=
      Ideal.mem_span_singleton.2 (dvd_trans (pow_dvd_pow _ (Nat.le_add_right k c₀))
        (Ideal.mem_span_singleton.1 ham))
    have h6 := Ideal.add_mem _ ham' h4
    rw [sub_add_cancel, map_pow] at h6
    exact (Ideal.mul_unit_mem_iff_mem _ (W.EE_π.pow m)).1 h6
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {((PD.p : ℕ) : W.EE)}) W.EE) x
    fun k => ?_
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  exact key k

theorem smul_cancel [IsDomain O] [IsDiscreteValuationRing O] (κ : PowerSeries O) (hκ : κ ≠ 0)
    (x y : C.V) (h : κ • x = κ • y) : x = y := by
  have hz : (baseIdOf hR).d κ • C.t 0 (x - y) = 0 := by
    rw [← C.t_smul, smul_sub, h, sub_self, C.t_zero]
  have hz' : algebraMap (LetA O n) W.EE ((baseIdOf hR).d κ) • C.t 0 (x - y) = 0 := by
    rw [algebraMap_smul]
    exact hz
  have := (W.DD_free T).1
  have h0 : C.t 0 (x - y) = 0 := by
    apply (Module.Free.chooseBasis W.EE (W.DD T)).repr.injective
    ext k
    have h2 := congrArg (fun z => (Module.Free.chooseBasis W.EE (W.DD T)).repr z k) hz'
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at h2
    rw [map_zero, Finsupp.zero_apply]
    exact isRegular_image_in_EE hR hκ _ h2
  exact sub_eq_zero.1 (C.t_inj 0 (by rw [h0, C.t_zero]))

end Formalism.MainNotions.N.Ln03.K8
end
end

