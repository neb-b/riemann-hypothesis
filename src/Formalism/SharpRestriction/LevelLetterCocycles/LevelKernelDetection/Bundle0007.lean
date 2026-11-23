module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0027
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0029

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfMapFl
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

section General

variable {LL Qp : Type} [Field LL] [Field Qp] [Algebra Qp LL]
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
  [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]
  {B₁ B₂ : Type} [AddCommGroup B₁] [Module Qp B₁] [AddCommGroup B₂] [Module Qp B₂]

theorem pfMapFl_map_comm (f : V₁ →ₗ[LL] V₂) (g : B₁ →ₗ[Qp] B₂) (z : V₁ ⊗[Qp] B₁) :
    AlgebraTensorModule.map f (LinearMap.id : B₂ →ₗ[Qp] B₂)
        (AlgebraTensorModule.map (LinearMap.id : V₁ →ₗ[LL] V₁) g z) =
      AlgebraTensorModule.map (LinearMap.id : V₂ →ₗ[LL] V₂) g
        (AlgebraTensorModule.map f (LinearMap.id : B₁ →ₗ[Qp] B₁) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end General

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

section Filt

variable {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)

abbrev pfMapFl_Fb : T₁.V ⊗[Qp] B →ₗ[LL] T₂.V ⊗[Qp] B :=
  AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B)

abbrev pfMapFl_FdR : T₁.V ⊗[Qp] BdR →ₗ[LL] T₂.V ⊗[Qp] BdR :=
  AlgebraTensorModule.map F.f (LinearMap.id : BdR →ₗ[Qp] BdR)

theorem pfMapFl_ιV (z : T₁.V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := T₂.V) (pfMapFl_Fb F z) =
      pfMapFl_FdR F (ιV PD (LL := LL) (V := T₁.V) z) :=
  (pfMapFl_map_comm F.f (PD.ι.toLinearMap.restrictScalars Qp) z).symm

theorem pfMapFl_φ (z : T₁.V ⊗[Qp] B) :
    φVB PD (LL := LL) (V := T₂.V) (pfMapFl_Fb F z) =
      pfMapFl_Fb F (φVB PD (LL := LL) (V := T₁.V) z) :=
  (pfMapFl_map_comm F.f PD.φ.toLinearMap z).symm

theorem pfMapFl_φpow (s : ℕ) (z : T₁.V ⊗[Qp] B) :
    ((φVB PD (LL := LL) (V := T₂.V) : Module.End LL (T₂.V ⊗[Qp] B)) ^ s)
        (pfMapFl_Fb F z) =
      pfMapFl_Fb F (((φVB PD (LL := LL) (V := T₁.V) : Module.End LL (T₁.V ⊗[Qp] B)) ^ s) z) := by
  induction s generalizing z with
  | zero => rfl
  | succ s ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, pfMapFl_φ, ih]

theorem pfMapFl_act (g : G) (z : T₁.V ⊗[Qp] B) :
    actVB PD T₂.ρ g (pfMapFl_Fb F z) = pfMapFl_Fb F (actVB PD T₁.ρ g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [actVB, F.equiv]
  | add x y hx hy =>
    simp only [map_add (f := _)]
    rw [hx, hy]

theorem pfMapFl_dcris (z : T₁.V ⊗[Qp] B) (hz : z ∈ Dcris PD T₁.ρ) :
    pfMapFl_Fb F z ∈ Dcris PD T₂.ρ := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hz ⊢
  intro g
  rw [pfMapFl_act, hz g]

theorem pfMapFl_dcrisL (τ₀ : K₀ →ₐ[Qp] LL) (z : T₁.V ⊗[Qp] B) (hz : z ∈ DcrisL PD T₁.ρ τ₀) :
    pfMapFl_Fb F z ∈ DcrisL PD T₂.ρ τ₀ := by
  rw [DcrisL, Submodule.mem_inf] at hz ⊢
  refine ⟨pfMapFl_dcris F z hz.1, ?_⟩
  have h2 := hz.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at h2 ⊢
  intro c
  have h3 : mulVB (K₀ := K₀) (B := B) (V := T₂.V) (LL := LL) c (pfMapFl_Fb F z) =
      pfMapFl_Fb F (mulVB (K₀ := K₀) (B := B) (V := T₁.V) (LL := LL) c z) :=
    (pfMapFl_map_comm F.f (LinearMap.mulLeft Qp (algebraMap K₀ B c)) z).symm
  rw [h3, h2 c, map_smul]

theorem pfMapFl_filV (a : ℤ) (z : T₁.V ⊗[Qp] BdR) (hz : z ∈ FilV PD (LL := LL) (V := T₁.V) a) :
    pfMapFl_FdR F z ∈ FilV PD (LL := LL) (V := T₂.V) a := by
  obtain ⟨w, rfl⟩ := hz
  exact ⟨AlgebraTensorModule.map F.f LinearMap.id w,
    (pfMapFl_map_comm F.f ((PD.Fil a).restrictScalars Qp).subtype w).symm⟩

theorem pfMapFl_filCris (a : ℤ) (z : T₁.V ⊗[Qp] B) (hz : z ∈ FilCris PD T₁.ρ a) :
    pfMapFl_Fb F z ∈ FilCris PD T₂.ρ a := by
  rw [FilCris, Submodule.mem_inf, Submodule.mem_comap] at hz ⊢
  refine ⟨pfMapFl_dcris F z hz.1, ?_⟩
  rw [pfMapFl_ιV]
  exact pfMapFl_filV F a _ hz.2

theorem pfMapFl_filD {c : ZMod n} (h : MemD W F c) (s : ℕ) (u : ℤ) (x : Dc W T₁ c)
    (hx : x ∈ FilD W T₁ c s u) : dmapOf h x ∈ FilD W T₂ c s u := by
  have hx' : ιV PD (LL := LL) (V := T₁.V) (x : T₁.V ⊗[Qp] B) ∈ FilLev W T₁ c s u := hx
  obtain ⟨y', hy', hxy⟩ := Submodule.mem_map.1 hx'
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hy'
  show ιV PD (LL := LL) (V := T₂.V) (pfMapFl_Fb F (x : T₁.V ⊗[Qp] B)) ∈ FilLev W T₂ c s u
  refine Submodule.mem_map.2 ⟨_, Submodule.mem_map.2 ⟨pfMapFl_Fb F y,
    ⟨pfMapFl_filCris F u y hy.1, pfMapFl_dcrisL F _ y hy.2⟩, rfl⟩, ?_⟩
  rw [pfMapFl_φpow, pfMapFl_ιV, pfMapFl_ιV, hxy]

end Filt

section Xi

variable {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {c : ZMod n}

theorem pfMapFl_ambF_xi (h : MemD W F c) (s : ℕ) (x : Amb LL (KsW W s) (Dc W T₁ c))
    (hx : x ∈ Xi (KsW W s) (Tw (LL := LL) (D := Dc W T₁ c) 0)) :
    ambF h s x ∈ Xi (KsW W s) (Tw (LL := LL) (D := Dc W T₂ c) 0) := by
  have hx' : ∀ i, cf x i ∈ (Tw (LL := LL) (D := Dc W T₁ c) 0 i).baseChange (KsW W s) := hx
  show ∀ i, cf (ambF h s x) i ∈ (Tw (LL := LL) (D := Dc W T₂ c) 0 i).baseChange (KsW W s)
  intro i
  have hi := hx' i
  have hc : cf (ambF h s x) i = (dmapOf h).baseChange (KsW W s) (cf x i) := rfl
  rw [hc]
  unfold Tw at hi ⊢
  split_ifs at hi ⊢ with h0
  · rw [Submodule.baseChange_top]
    exact Submodule.mem_top
  · rw [Submodule.baseChange_bot, Submodule.mem_bot] at hi ⊢
    rw [hi, map_zero]

theorem pfMapFl_mem_FlS {hΔ : DeltaRho hR uZ ιZ c} {ell : ℕ} (Λ f' : PowerSeries O) (s : ℕ)
    (e : LvT hR uZ ιZ T₁ c hΔ ell) :
    e ∈ FlS (hR := hR) (uZ := uZ) (ιZ := ιZ) (T := T₁) (c := c) (hΔ := hΔ) (ell := ell) Λ f' s ↔
      ∃ x ∈ Xi (KsW W s) (Tw (LL := LL) (D := Dc W T₁ c) 0),
        prL s (Λ • e) = HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s f') • x := Iff.rfl

end Xi

section ThetaShiftProofs

variable {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁} {C₂ : Coord W (baseIdOf hR) T₂}
  {F : LatHom T₁.L T₂.L} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ} {κ₁ κ₂ : PowerSeries O} {r₁ r₂ : ℕ}
  {lam₁ : Fin r₁ → Dc W T₁ c} {lam₂ : Fin r₂ → Dc W T₂ c}

theorem mapFl_holds
    (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₁ lam₁)
    (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₂ lam₂)
    (Mh : MapHyp hR uZ ιZ F c) (j M g η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ) :
    ∀ s < ell, ∀ e ∈ (lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Fl s,
      prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell e ∈
        (lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Fl s := by
  intro s hs e he
  obtain ⟨x, hx, hex⟩ := (pfMapFl_mem_FlS (hΔ := Hy₁.delta)
    (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) ((baseIdOf hR).Bs.ff' ell j M g) s e).1 he
  refine (pfMapFl_mem_FlS (hΔ := Hy₂.delta)
    (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) ((baseIdOf hR).Bs.ff' ell j M g) s _).2
    ⟨ambF Mh.memD s x, pfMapFl_ambF_xi Mh.memD s x hx, ?_⟩
  have hsm := (prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell).map_smul
    (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) e
  erw [← hsm, prL_prEOf Mh s hs, hex, Mh.smul]

theorem cMap_holds (hD : MemD W F c) (kind : ℕ → Kind) (b : ℕ → ℕ) (η : ℕ)
    (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (hLamP : ∀ k, dmapOf hD (lam₁ k) = ∑ l, algebraMap O LL (LinearMap.toMatrix' P l k) • lam₂ l) :
    ∀ s < ell, kind s = Kind.up → Formalism.ExponentWindows.E.CMap (UL lam₁ kind b η s) (UL lam₂ kind b η s) P := by
  intro s _ hk w hw
  have hw' : ∑ k, algebraMap O LL (w k) • lam₁ k ∈ FilD W T₁ c s ((b s : ℕ) : ℤ) := by
    have := hw
    simp only [UL, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq,
      hk, UOf] at this
    exact this
  have hmap := pfMapFl_filD F hD s _ _ hw'
  have hsum : dmapOf hD (∑ k, algebraMap O LL (w k) • lam₁ k) =
      ∑ l, algebraMap O LL (P w l) • lam₂ l := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, hLamP, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_smul, ← LinearMap.toMatrix'_mulVec P w]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum]
    refine congrArg (· • lam₂ l) (Finset.sum_congr rfl fun k _ => ?_)
    rw [map_mul]
    ring
  rw [hsum] at hmap
  show ∑ l, algebraMap O LL (P w l) • lam₂ l ∈ UOf (kind s) (b s) η (FilD W T₂ c s)
  rw [hk]
  exact hmap

end ThetaShiftProofs

end Formalism.MainNotions.N.Ln03.Pf
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfMapLoc
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

theorem Pf_MapLoc_ιV_inj (T : LocLat G Qp LL O) : Function.Injective (ιV PD (LL := LL) (V := T.V)) := by
  have h : ∀ y, ιV PD (LL := LL) (V := T.V) y =
      ((PD.ι.toLinearMap.restrictScalars Qp).lTensor T.V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [ιV]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : Function.Injective (PD.ι.toLinearMap.restrictScalars Qp) := PD.ι_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab

theorem Pf_MapLoc_ιV_map {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (y : T₁.V ⊗[Qp] B) :
    AlgebraTensorModule.map F.f (LinearMap.id : BdR →ₗ[Qp] BdR) (ιV PD (LL := LL) (V := T₁.V) y) =
      ιV PD (LL := LL) (V := T₂.V) (AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [ιV]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem Pf_MapLoc_levB_map {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (crys₁ : IsCrys PD T₁.ρ) (crys₂ : IsCrys PD T₂.ρ)
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (i : ZMod n) (ζ : LL) (x : ↥(W.N T₁)) (hx : W.map F (x : W.DD T₁) ∈ W.N T₂) (k : ℤ) :
    Lb.levB T₂ i ζ ⟨W.map F (x : W.DD T₁), hx⟩ k =
      AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) (Lb.levB T₁ i ζ x k) := by
  apply Pf_MapLoc_ιV_inj (PD := PD) T₂
  rw [← levN_eq, W.levN_map F crys₁ crys₂ i ζ x hx k, levN_eq, Pf_MapLoc_ιV_map]

theorem Pf_MapLoc_toKsD_map (s : ℕ) {D₁ D₂ : Type} [AddCommGroup D₁] [Module LL D₁]
    [AddCommGroup D₂] [Module LL D₂] (g : D₁ →ₗ[LL] D₂) (f : Rs LL PD.p s → D₁) :
    g.baseChange (KsW W s) (toKsD W s D₁ f) = toKsD W s D₂ (fun ζ => g (f ζ)) := by
  classical
  obtain ⟨y, rfl⟩ := (TensorProduct.piScalarRight LL LL D₁ (Rs LL PD.p s)).surjective f
  have h1 : (fun ζ => g (TensorProduct.piScalarRight LL LL D₁ (Rs LL PD.p s) y ζ)) =
      TensorProduct.piScalarRight LL LL D₂ (Rs LL PD.p s) (g.rTensor _ y) := by
    induction y using TensorProduct.induction_on with
    | zero => funext ζ; simp
    | tmul x a => funext ζ; simp
    | add y y' hy hy' =>
      funext ζ
      have e1 := congrFun hy ζ
      have e2 := congrFun hy' ζ
      simp only [map_add (f := _), Pi.add_apply] at e1 e2 ⊢
      rw [e1, e2]
  simp only [toKsD, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.symm_apply_apply]
  rw [h1, LinearEquiv.symm_apply_apply]
  clear h1
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x a => simp [LinearMap.baseChange_tmul]
  | add y y' hy hy' => simp only [map_add (f := _), hy, hy']

theorem Pf_MapLoc_ambF_expN (s : ℕ) {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {c : ZMod n}
    (h : MemD W F c) (x : ↥(W.N T₁)) (y : ↥(W.N T₂))
    (hxy : ∀ (ζ : LL) (k : ℤ), Lb.levB T₂ c ζ y k =
      AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) (Lb.levB T₁ c ζ x k)) :
    ambF h s (expN Lb s T₁ c x) = expN Lb s T₂ c y := by
  have hc : ∀ k, (dmapOf h).baseChange (KsW W s) (coefN Lb s T₁ c x k) = coefN Lb s T₂ c y k := by
    intro k
    simp only [coefN]
    rw [Pf_MapLoc_toKsD_map]
    congr 1
    funext ζ
    apply Subtype.ext
    exact (hxy ζ.1 k).symm
  apply (HahnModule.of (KsW W s)).symm.injective
  ext k
  simp [ambF, ambMap, expN, HahnSeries.ofSuppBddBelow, hc]

section ThetaShiftProofs

variable {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁} {C₂ : Coord W (baseIdOf hR) T₂}
  {F : LatHom T₁.L T₂.L} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ} {κ₁ κ₂ : PowerSeries O} {r₁ r₂ : ℕ}
  {lam₁ : Fin r₁ → Dc W T₁ c} {lam₂ : Fin r₂ → Dc W T₂ c}

theorem locComm_holds (hC : CoordHom C₁ C₂ F)
    (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₁ lam₁)
    (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₂ lam₂)
    (Mh : MapHyp hR uZ ιZ F c) (j M g η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ)
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (kap₁_unit : ∀ s < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ₁)))
    (kap₂_unit : ∀ s < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ₂))) :
    ∀ s < ell, ∀ (w : C₁.V)
    (hw : w ∈ (latOf C₁).W c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell))
    (hw' : (latHomOf hC).f w ∈ (latOf C₂).W c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell)),
    prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell
        ((lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).loc s ⟨w, hw⟩) =
      (lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).loc s ⟨(latHomOf hC).f w, hw'⟩ := by
  intro s _ w hw hw'
  refine funext fun ⟨s', hs'⟩ => Subtype.ext ?_
  show ambF Mh.memD s' (locF Lb C₁ κ₁ s' (κ₁ • w) _) = locF Lb C₂ κ₂ s' (κ₂ • hC.f w) _
  have hm₁ : C₂.t c (κ₁ • hC.f w) ∈ W.N T₂ := by
    have h0 := (latHomOf hC).map_N c (κ₁ • w) (Hy₁.kap w hw)
    rw [show (latHomOf hC).f (κ₁ • w) = κ₁ • hC.f w from hC.f.map_smul κ₁ w] at h0
    exact (mem_N C₂ c _).1 h0
  have hm₂ : C₂.t c (κ₂ • hC.f w) ∈ W.N T₂ := (mem_N C₂ c _).1 (Hy₂.kap _ hw')
  have hA : ambF Mh.memD s' (expN Lb s' T₁ c ⟨C₁.t c (κ₁ • w), Hy₁.kap w hw⟩) =
      expN Lb s' T₂ c ⟨C₂.t c (κ₁ • hC.f w), hm₁⟩ := by
    apply Pf_MapLoc_ambF_expN
    intro ζ k
    have hx : W.map F (C₁.t c (κ₁ • w)) ∈ W.N T₂ := by
      rw [← hC.coord_hom_map_trace, map_smul]
      exact hm₁
    have he : (⟨C₂.t c (κ₁ • hC.f w), hm₁⟩ : ↥(W.N T₂)) = ⟨W.map F (C₁.t c (κ₁ • w)), hx⟩ :=
      Subtype.ext (by
        show C₂.t c (κ₁ • hC.f w) = W.map F (C₁.t c (κ₁ • w))
        rw [← hC.coord_hom_map_trace, map_smul])
    rw [he]
    exact Pf_MapLoc_levB_map F hC.crys hC.crys' levN_eq c ζ ⟨C₁.t c (κ₁ • w), Hy₁.kap w hw⟩ hx k
  have hs₁ : (baseIdOf hR).d κ₂ • C₂.t c (κ₁ • hC.f w) ∈ W.N T₂ := (W.N T₂).smul_mem _ hm₁
  have hs₂ : (baseIdOf hR).d κ₁ • C₂.t c (κ₂ • hC.f w) ∈ W.N T₂ := (W.N T₂).smul_mem _ hm₂
  have hE : HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ₂) •
        expN Lb s' T₂ c ⟨C₂.t c (κ₁ • hC.f w), hm₁⟩ =
      HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ₁) •
        expN Lb s' T₂ c ⟨C₂.t c (κ₂ • hC.f w), hm₂⟩ := by
    rw [← Hy₂.expSemi s' κ₂ ⟨_, hm₁⟩ hs₁, ← Hy₂.expSemi s' κ₁ ⟨_, hm₂⟩ hs₂]
    congr 1
    apply Subtype.ext
    change (baseIdOf hR).d κ₂ • C₂.t c (κ₁ • hC.f w) = (baseIdOf hR).d κ₁ • C₂.t c (κ₂ • hC.f w)
    rw [← C₂.t_smul, ← C₂.t_smul, smul_smul, smul_smul, mul_comm]
  unfold locF
  rw [Mh.smul s', hA]
  set ρ₁ := HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ₁)
  set ρ₂ := HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ₂)
  calc Ring.inverse ρ₁ • expN Lb s' T₂ c ⟨C₂.t c (κ₁ • hC.f w), hm₁⟩
      = (Ring.inverse ρ₁ * Ring.inverse ρ₂) • (ρ₂ • expN Lb s' T₂ c ⟨C₂.t c (κ₁ • hC.f w), hm₁⟩) := by
        rw [smul_smul, mul_assoc, Ring.inverse_mul_cancel ρ₂ (kap₂_unit s' hs'), mul_one]
    _ = (Ring.inverse ρ₁ * Ring.inverse ρ₂) • (ρ₁ • expN Lb s' T₂ c ⟨C₂.t c (κ₂ • hC.f w), hm₂⟩) := by
        rw [hE]
    _ = Ring.inverse ρ₂ • expN Lb s' T₂ c ⟨C₂.t c (κ₂ • hC.f w), hm₂⟩ := by
        rw [smul_smul, mul_comm (Ring.inverse ρ₁), mul_assoc, Ring.inverse_mul_cancel ρ₁ (kap₁_unit s' hs'),
          mul_one]

end ThetaShiftProofs

end Formalism.MainNotions.N.Ln03.Pf
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfUTieRec
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Module IsLocalRing Formalism.MainNotions.N.Ln03

theorem zpEquiv_apply_symm {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (x : ℤ_[q]) :
    zpEquiv h (zpEquiv h.symm x) = x := by
  subst h
  rfl

theorem zpEquiv_valuation {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (x : ℤ_[q]) :
    (zpEquiv h.symm x).valuation = x.valuation := by
  subst h
  rfl

section Loc

variable {l : ℕ} [Fact l.Prime]

theorem norm_chiQ_le (P : LocPrime l) (g : GQ l) : ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
  obtain ⟨a, ha, -⟩ := P.χQ_cyc g 0 1 (by simp)
  have h1 : ‖((a : ℕ) : ℚ_[l])‖ ≤ 1 := by
    rw [← PadicInt.coe_natCast]
    exact PadicInt.norm_le_one _
  have ha' : ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])‖ ≤ 1 := by simpa using ha
  calc ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖
      = ‖(((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) + (a : ℚ_[l])‖ := by rw [sub_add_cancel]
    _ ≤ max ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])‖ ‖(a : ℚ_[l])‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le ha' h1

theorem norm_chiQ (P : LocPrime l) (g : GQ l) : ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖ = 1 := by
  have h1 := norm_chiQ_le P g
  have h2 := norm_chiQ_le P g⁻¹
  have hm : ((P.χQ g⁻¹ : ℚ_[l]ˣ) : ℚ_[l]) * ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hn : ‖((P.χQ g⁻¹ : ℚ_[l]ˣ) : ℚ_[l])‖ * ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖ = 1 := by
    rw [← norm_mul, hm, norm_one]
  refine le_antisymm h1 ?_
  nlinarith [norm_nonneg ((P.χQ g⁻¹ : ℚ_[l]ˣ) : ℚ_[l]), norm_nonneg ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])]

theorem v_algebraMap_zp (P : LocPrime l) (LL : FinExt l) (y : ℤ_[l]) (hy : y ≠ 0) :
    P.v LL (algebraMap ℤ_[l] ↥LL.1 y) = ((y.valuation : ℕ) : WithTop ℚ) := by
  have hint : ∀ z : ℤ_[l], 0 ≤ P.v LL (algebraMap ℤ_[l] ↥LL.1 z) := fun z =>
    (P.v_O LL _).2 (Subalgebra.algebraMap_mem (OL LL) z)
  have spec := PadicInt.unitCoeff_spec hy
  set w := PadicInt.unitCoeff hy
  have hw : P.v LL (algebraMap ℤ_[l] ↥LL.1 (w : ℤ_[l])) = 0 := by
    have h1 := hint (w : ℤ_[l])
    have h2 := hint ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
    have hsum : P.v LL (algebraMap ℤ_[l] ↥LL.1 (w : ℤ_[l])) +
        P.v LL (algebraMap ℤ_[l] ↥LL.1 ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
        AddValuation.map_one]
    exact le_antisymm ((le_add_of_nonneg_right h2).trans hsum.le) h1
  conv_lhs => rw [spec]
  rw [map_mul, map_pow, map_natCast, AddValuation.map_mul, AddValuation.map_pow, hw, P.v_l, zero_add,
    nsmul_one]

end Loc

theorem uTieRec_holds (D : D7) (HW : HWOf D.loc) : UTieRec D HW := by
  intro l _ K LL h _
  obtain ⟨g0, hg0⟩ := ((HW l).W K 1 LL h.2.2).resΓ_onto ((HW l).W K 1 LL h.2.2).gam
  have hres := ((HW l).W K 1 LL h.2.2).χΓ_res g0
  rw [hg0] at hres
  have hn : ‖((((D.loc l).PD K).χ g0 : ℚ_[l]ˣ) : ℚ_[l])‖ = 1 := by
    rw [(D.loc l).PD_χ]
    exact norm_chiQ (D.loc l) _
  set u : ℤ_[l]ˣ := PadicInt.mkUnits hn with hu
  have hu' : ((u : ℤ_[l]) : ℚ_[l]) = ((((D.loc l).PD K).χ g0 : ℚ_[l]ˣ) : ℚ_[l]) := PadicInt.mkUnits_eq hn
  have hχ : ((((HW l).W K 1 LL h.2.2).χΓ ((HW l).W K 1 LL h.2.2).gam : ↥(OL LL)) : ↥LL.1) =
      algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l]) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1, PadicInt.algebraMap_apply, hu']
    exact hres
  refine ⟨Units.map (zpEquiv ((D.loc l).PD_p K).symm).toRingHom.toMonoidHom u, ?_, ?_⟩
  · show (zpEquiv ((D.loc l).PD_p K).symm (u : ℤ_[l]) - 1).valuation = 1
    rw [← map_one (zpEquiv ((D.loc l).PD_p K).symm), ← map_sub, zpEquiv_valuation ((D.loc l).PD_p K)]
    have hg := ((HW l).W K 1 LL h.2.2).gam_gen
    rw [(HW l).W_s K 1 LL h.2.2] at hg
    change (D.loc l).v LL ((((HW l).W K 1 LL h.2.2).χΓ ((HW l).W K 1 LL h.2.2).gam : ↥(OL LL)) - 1) =
      ((1 : ℕ) : WithTop ℚ) at hg
    rw [hχ, ← map_one (algebraMap ℤ_[l] ↥LL.1), ← map_sub] at hg
    have hne : (u : ℤ_[l]) - 1 ≠ 0 := by
      intro h0
      rw [h0, map_zero, AddValuation.map_zero] at hg
      exact WithTop.top_ne_coe hg
    rw [v_algebraMap_zp (D.loc l) LL _ hne] at hg
    exact_mod_cast hg
  · apply Subtype.ext
    show ((algebraMap ℤ_[l] ↥(OL LL) (zpEquiv ((D.loc l).PD_p K)
      (zpEquiv ((D.loc l).PD_p K).symm (u : ℤ_[l])))) : ↥LL.1) = _
    rw [zpEquiv_apply_symm, hχ]
    rfl

end Formalism.MainNotions.N.Ln03.Pf
end
end

