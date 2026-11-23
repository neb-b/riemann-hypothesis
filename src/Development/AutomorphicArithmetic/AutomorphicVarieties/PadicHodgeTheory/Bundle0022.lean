module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmBilin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MatrixExtendByZeroApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0019

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DeformCr
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.DeformationPairing

private def extRep {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) :
    Representation A G (V × A) where
  toFun g := ((ρ g).comp (LinearMap.fst A V A) + (LinearMap.snd A V A).smulRight (c g)).prod (LinearMap.snd A V A)
  map_one' := by
    have h1 : c 1 = 0 := by simpa using hc 1 1
    refine LinearMap.ext fun x => ?_
    simp [h1]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    simp [hc, add_assoc, add_comm, add_left_comm]

private theorem extRep_apply {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (g : G) (x : V × A) :
    extRep ρ c hc g x = (ρ g x.1 + x.2 • c g, x.2) := rfl

private theorem contAction_sub {G A V : Type} [Group G] [TopologicalSpace G] [CommRing A] [AddCommGroup V]
    [Module A V] [TopologicalSpace V] (ρ : Representation A G V) (h : ContAction ρ) (H : Subgroup G) :
    ContAction (ρ.comp H.subtype : Representation A H V) :=
  h.comp (f := fun p : H × V => ((p.1 : G), p.2))
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

private noncomputable def pair (Q : Type) {E : Type} [Field Q] [Field E] [Algebra Q E] (n : ℕ) :
    (Matrix (Fin n) (Fin n) E × E) →ₗ[Q] (Fin n → E) →ₗ[Q] (Fin n → DualNumber E) :=
  LinearMap.mk₂ Q (fun w v i => (⟨w.2 * v i, (w.1.mulVec v) i⟩ : DualNumber E))
    (fun w w' v => by
      funext i; refine TrivSqZeroExt.ext ?_ ?_ <;> simp [add_mul, Matrix.add_mulVec] <;> rfl)
    (fun c w v => by
      funext i; refine TrivSqZeroExt.ext ?_ ?_ <;> simp [Matrix.smul_mulVec] <;> rfl)
    (fun w v v' => by
      funext i; refine TrivSqZeroExt.ext ?_ ?_ <;> simp [mul_add, Matrix.mulVec_add] <;> rfl)
    (fun c w v => by
      funext i; refine TrivSqZeroExt.ext ?_ ?_ <;> simp [Matrix.mulVec_smul] <;> rfl)

private theorem pair_fst (Q : Type) {E : Type} [Field Q] [Field E] [Algebra Q E] (n : ℕ)
    (w : Matrix (Fin n) (Fin n) E × E) (v : Fin n → E) (i : Fin n) : (pair Q n w v i).fst = w.2 * v i := rfl

private theorem pair_snd (Q : Type) {E : Type} [Field Q] [Field E] [Algebra Q E] (n : ℕ)
    (w : Matrix (Fin n) (Fin n) E × E) (v : Fin n → E) (i : Fin n) :
    (pair Q n w v i).snd = (w.1.mulVec v) i := rfl

private theorem mulVec_fst {E : Type} [Field E] {n : ℕ} (R S : Matrix (Fin n) (Fin n) E)
    (R' : Matrix (Fin n) (Fin n) (DualNumber E)) (h : ∀ i j, R' i j = ⟨R i j, S i j⟩)
    (w : Fin n → DualNumber E) (i : Fin n) :
    (R'.mulVec w i).fst = R.mulVec (fun j => (w j).fst) i := by
  have h1 : ∀ i j, (R' i j).fst = R i j := fun i j => by rw [h]; rfl
  simp [Matrix.mulVec, dotProduct, TrivSqZeroExt.fst_sum, h1]

private theorem mulVec_snd {E : Type} [Field E] {n : ℕ} (R S : Matrix (Fin n) (Fin n) E)
    (R' : Matrix (Fin n) (Fin n) (DualNumber E)) (h : ∀ i j, R' i j = ⟨R i j, S i j⟩)
    (w : Fin n → DualNumber E) (i : Fin n) :
    (R'.mulVec w i).snd = R.mulVec (fun j => (w j).snd) i + S.mulVec (fun j => (w j).fst) i := by
  have h1 : ∀ i j, (R' i j).fst = R i j := fun i j => by rw [h]; rfl
  have h2 : ∀ i j, (R' i j).snd = S i j := fun i j => by rw [h]; rfl
  simp [Matrix.mulVec, dotProduct, TrivSqZeroExt.snd_sum, h1, h2, Finset.sum_add_distrib]

private theorem ad_mulVec {G E : Type} [Group G] [Field E] {n : ℕ} (r : G →* GL (Fin n) E) (g : G)
    (X : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    (adGL r g X).mulVec (colRep r g v) = colRep r g (X.mulVec v) := by
  change ((r g : Matrix (Fin n) (Fin n) E) * X * ((r g)⁻¹ : GL (Fin n) E)).mulVec
    (Matrix.toLin' (r g : Matrix (Fin n) (Fin n) E) v) = Matrix.toLin' (r g : Matrix (Fin n) (Fin n) E) _
  simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

end UpperTheory.V.Loc.DeformationPairing

open UpperTheory.V.Loc.DeformationPairing in
theorem UpperTheory.V.Loc.deformCr :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] {n : ℕ} (r : G →* GL (Fin n) E), Continuous (fun g => (r g : Matrix (Fin n) (Fin n) E)) → ∀ y ∈ Z1 (adGL r), ∀ r' : G →* GL (Fin n) (DualNumber E), (∀ g i j, (r' g : Matrix (Fin n) (Fin n) (DualNumber E)) i j = ⟨(r g : Matrix (Fin n) (Fin n) E) i j, (y g * (r g : Matrix (Fin n) (Fin n) E)) i j⟩) → ∀ (H : Subgroup G) [H.Normal], IsOpen (H : Set G) → (CrOn φ (colRep r') H ↔ CrOn φ (colRep r) H ∧ y ∈ UpperTheory.V.Loc.finiteCocycles φ (adGL r)) := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ _ n r hr y hy r' hr' H _ hH
  haveI : IsModuleTopology ℚ_[l] (DualNumber E) := inferInstanceAs (IsModuleTopology ℚ_[l] (E × E))
  haveI : FiniteDimensional ℚ_[l] (DualNumber E) := inferInstanceAs (FiniteDimensional ℚ_[l] (E × E))
  haveI : IsModuleTopology ℚ_[l] (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (IsModuleTopology ℚ_[l] (Fin n → Fin n → E))
  have hψ : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  have cV : ContAction (colRep r) :=
    Continuous.matrix_mulVec (hr.comp continuous_fst) continuous_snd
  have hr'c : Continuous (fun g => (r' g : Matrix (Fin n) (Fin n) (DualNumber E))) := by
    refine continuous_matrix fun i j => ?_
    simp only [hr']
    exact (hr.matrix_elem i j).prodMk ((hy.1.matrix_mul hr).matrix_elem i j)
  have cW : ContAction (colRep r') :=
    Continuous.matrix_mulVec (hr'c.comp continuous_fst) continuous_snd
  have cM : ContAction (adGL r) := by
    have hi : Continuous (fun g => (((r g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) := by
      simp only [← map_inv]
      exact hr.comp continuous_inv
    exact ((hr.comp continuous_fst).matrix_mul continuous_snd).matrix_mul (hi.comp continuous_fst)
  have cH : ContAction (extRep (adGL r) y hy.2) := by
    unfold ReciprocityTheory.Gal.ContAction
    simp only [extRep_apply]
    refine Continuous.prodMk (Continuous.add ?_ ?_) (continuous_snd.comp continuous_snd)
    · exact Continuous.comp (f := fun p : G × (Matrix (Fin n) (Fin n) E × E) => (p.1, p.2.1)) cM (by fun_prop)
    · exact (continuous_snd.comp continuous_snd).smul (hy.1.comp continuous_fst)
  have hb : ∀ g w v, pair ℚ_[l] n (extRep (adGL r) y hy.2 g w) (colRep r g v)
      = colRep r' g (pair ℚ_[l] n w v) := by
    intro g w v
    funext i
    have e' : colRep r' g (pair ℚ_[l] n w v)
      = (r' g : Matrix (Fin n) (Fin n) (DualNumber E)).mulVec (pair ℚ_[l] n w v) := rfl
    have e : ∀ u, colRep r g u = (r g : Matrix (Fin n) (Fin n) E).mulVec u := fun _ => rfl
    have e1 : (fun j => (pair ℚ_[l] n w v j).fst) = w.2 • v := rfl
    have e2 : (fun j => (pair ℚ_[l] n w v j).snd) = w.1.mulVec v := rfl
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [e', mulVec_fst _ _ _ (hr' g), e1, pair_fst, extRep_apply, Matrix.mulVec_smul, e]; rfl
    · rw [e', mulVec_snd _ _ _ (hr' g), e1, e2, pair_snd, extRep_apply, Matrix.add_mulVec, ad_mulVec, e, e,
        Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      rfl
  have crM : CrOn φ (colRep r) H → CrOn φ (adGL r) H := fun h =>
    (isCrys_isDR_internalHom (φ.comp H.subtype) hψ _ _ _ (contAction_sub _ cV H) (contAction_sub _ cV H) (contAction_sub _ cM H)
      (LinearMap.mk₂ ℚ_[l] (fun (X : Matrix (Fin n) (Fin n) E) (v : Fin n → E) => X.mulVec v)
        (fun _ _ _ => Matrix.add_mulVec _ _ _) (fun _ _ _ => Matrix.smul_mulVec _ _ _)
        (fun _ _ _ => Matrix.mulVec_add _ _ _) (fun _ _ _ => Matrix.mulVec_smul _ _ _))
      (fun g X v => ad_mulVec r g X v)
      (fun X Y hXY => Matrix.ext_iff_mulVec.2 fun v => LinearMap.congr_fun hXY v)).1 h h
  have cr1 : CrOn φ (chRep (1 : G →* Eˣ)) H :=
    crUnr (A := ℚ_[l]) (φ.comp H.subtype) hψ
      (resCoef ℚ_[l] ((chRep (1 : G →* Eˣ)).comp H.subtype : Representation E H E))
      (by
        unfold ReciprocityTheory.Gal.ContAction
        simpa [resCoef, chRep] using continuous_snd) 0
      (fun g _ x => by simp [resCoef, chRep])
  have htw : twist (1 : G →* Eˣ)⁻¹ (adGL r) = adGL r := by
    refine MonoidHom.ext fun g => ?_
    simp [twist]
  have key : CrOn φ (colRep r) H →
      (CrOn φ (extRep (adGL r) y hy.2) H ↔ y ∈ UpperTheory.V.Loc.finiteCocycles φ (adGL r)) := fun h => by
    have := crExt φ hφ (adGL r) (extRep (adGL r) y hy.2) cM cH 1 (LinearMap.inl E _ E) (LinearMap.snd E _ E)
      (0, 1) y LinearMap.inl_injective (Function.Exact.inl_snd) rfl
      (fun g x => by simp [extRep_apply]) (fun g => by simp [extRep_apply]) H hH (crM h) cr1
    rwa [htw] at this
  constructor
  · intro hW
    have hV : CrOn φ (colRep r) H := by
      refine ((isCrys_isDR_sub_quot (φ.comp H.subtype) hψ _ _ (contAction_sub _ cW H) (contAction_sub _ cV H)
        (((TrivSqZeroExt.fstHom ℚ_[l] E E).toLinearMap).compLeft (Fin n)) (fun g x => ?_)).2 (fun v => ?_)).1 hW
      · funext i
        exact mulVec_fst _ _ _ (hr' g) x i
      · exact ⟨fun i => TrivSqZeroExt.inl (v i), rfl⟩
    refine ⟨hV, ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : y = 0 := Subsingleton.elim _ _
      rw [this]; exact Submodule.zero_mem _
    · refine (key hV).1 ?_
      refine (isCrys_isDR_internalHom (A := ℚ_[l]) (φ.comp H.subtype) hψ
        (resCoef ℚ_[l] ((colRep r).comp H.subtype : Representation E H _))
        (resCoef ℚ_[l] ((colRep r').comp H.subtype : Representation (DualNumber E) H _))
        (resCoef ℚ_[l] ((extRep (adGL r) y hy.2).comp H.subtype : Representation E H _))
        (contAction_sub _ cV H) (contAction_sub _ cW H) (contAction_sub _ cH H) (pair ℚ_[l] n)
        (fun g w v => hb g w v) (fun w w' h => ?_)).1 hV hW
      refine Prod.ext (Matrix.ext_iff_mulVec.2 fun v => funext fun i => ?_) ?_
      · rw [← pair_snd ℚ_[l], ← pair_snd ℚ_[l], h]
      · have := pair_fst ℚ_[l] n w 1 ⟨0, hn⟩
        rw [h, pair_fst] at this
        simpa using this.symm
  · rintro ⟨hV, hy'⟩
    refine (admissible_of_bilinear_openSubgroup_galois (A := ℚ_[l]) (φ.comp H.subtype) hψ
        (resCoef ℚ_[l] ((extRep (adGL r) y hy.2).comp H.subtype : Representation E H _))
        (resCoef ℚ_[l] ((colRep r).comp H.subtype : Representation E H _))
        (resCoef ℚ_[l] ((colRep r').comp H.subtype : Representation (DualNumber E) H _))
        (contAction_sub _ cH H) (contAction_sub _ cV H) (contAction_sub _ cW H) (pair ℚ_[l] n)
        (fun g w v => hb g w v) ?_).1 ((key hV).2 hy') hV
    refine eq_top_iff.2 fun x _ => ?_
    have : x = pair ℚ_[l] n (0, 1) (fun i => (x i).fst) + pair ℚ_[l] n (1, 0) (fun i => (x i).snd) := by
      funext i
      refine TrivSqZeroExt.ext ?_ ?_ <;> simp [pair_fst, pair_snd]
    rw [this]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨(_, _), rfl⟩) (Submodule.subset_span ⟨(_, _), rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsNeOne
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem sandwich {E M : Type} [Field E] [AddCommGroup M] [Module E M] (B S Z : Submodule E M)
    (hBS : B ≤ S) (hSZ : S ≤ Z) [Module.Finite E B]
    [hQ : Module.Finite E ↥((S.comap Z.subtype).map (B.comap Z.subtype).mkQ)] :
    Module.Finite E S ∧
      finrank E S = finrank E ↥((S.comap Z.subtype).map (B.comap Z.subtype).mkQ) + finrank E B := by
  let f : S →ₗ[E] (Z ⧸ B.comap Z.subtype) := (B.comap Z.subtype).mkQ ∘ₗ Submodule.inclusion hSZ
  have hr : LinearMap.range f = (S.comap Z.subtype).map (B.comap Z.subtype).mkQ := by
    rw [LinearMap.range_comp, Submodule.range_inclusion]
  have hk : LinearMap.ker f = B.comap S.subtype := by
    ext x
    simp [f]
  have eB := Submodule.comapSubtypeEquivOfLe hBS
  have hkf : Module.Finite E ↥(LinearMap.ker f) := by
    rw [hk]; exact Module.Finite.equiv eB.symm
  have hrf : Module.Finite E ↥(LinearMap.range f) := by rw [hr]; exact hQ
  have hS : Module.Finite E S := by
    rw [Module.finite_def]
    refine Submodule.fg_of_fg_map_of_fg_inf_ker f ?_ ?_
    · rw [Submodule.map_top]; exact Module.Finite.iff_fg.1 hrf
    · rw [top_inf_eq]; exact Module.Finite.iff_fg.1 hkf
  refine ⟨hS, ?_⟩
  rw [← LinearMap.finrank_range_add_finrank_ker f, hr, hk, eB.finrank_eq]

private theorem exists_ne_one {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] ℚ_[l] E] (κ : G →* Eˣ) (w : ℤ) (hw : w ≠ 0) (h : HasWeight φ κ w) :
    ∃ g, κ g ≠ 1 := by
  obtain ⟨U, hU, h⟩ := h
  obtain ⟨-, s, ⟨⟨g, hg, rfl⟩, hs⟩, hfin⟩ := (cycInertia l).2 (U.map φ) (hφ.isOpenMap _ hU)
  refine ⟨g, fun h1 => hfin ?_⟩
  have hinj : Function.Injective (algebraMap ℤ_[l] E) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
    exact (algebraMap ℚ_[l] E).injective.comp Subtype.val_injective
  have h2 := h g hg hs
  rw [h1] at h2
  have h3 : cyc l l (φ g) ^ w = 1 := by
    apply Units.map_injective (f := (algebraMap ℤ_[l] E : ℤ_[l] →* E)) hinj
    rw [map_zpow, map_one]
    exact h2.symm
  exact isOfFinOrder_iff_zpow_eq_one.2 ⟨w, hw, h3⟩

private theorem finrank_ddr {l : ℕ} [Fact l.Prime] {G : Type} [Group G]
    (φ : G →* GQ l) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (ρ : Representation E G E) (h : IsDr φ ρ) : finrank E ↥(Ddr φ ρ) = φ.range.index := by
  have he : Ddr φ (resCoef ℚ_[l] ρ) = (Ddr φ ρ).restrictScalars ℚ_[l] := by
    ext x
    simp only [Ddr, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker]
    rfl
  have h1 : finrank ℚ_[l] ↥(Ddr φ ρ) = φ.range.index * finrank ℚ_[l] E := by
    unfold IsDr at h
    rw [he] at h
    exact h
  rw [← Module.finrank_mul_finrank ℚ_[l] E, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h1

theorem UpperTheory.V.Loc.z1fChar :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] (κ : G →* Eˣ), Continuous (fun g => (κ g : E)) → ∀ w : ℤ, HasWeight φ κ w → (w < 0 → UpperTheory.V.Loc.finiteCocycles φ (chRep κ) = ReciprocityTheory.Gal.B1 (chRep κ) ∧ finrank E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) = 1) ∧ (0 < w → Module.Finite E ↥(UpperTheory.V.Loc.finiteCocycles φ (chRep κ)) ∧ finrank E ↥(UpperTheory.V.Loc.finiteCocycles φ (chRep κ)) = φ.range.index + 1) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ _ _ _ κ hκ w hw
  have hc : ReciprocityTheory.Gal.ContAction (chRep κ) := by
    have : (fun p : G × E => chRep κ p.1 p.2) = fun p => (κ p.1 : E) * p.2 := by
      funext p; simp [chRep]
    unfold ReciprocityTheory.Gal.ContAction
    rw [this]
    exact (hκ.comp continuous_fst).mul continuous_snd
  obtain ⟨hdr, hfil⟩ := charFil φ hφ κ hκ w hw
  obtain ⟨hfin, hdim⟩ := bkDim hP φ hφ (chRep κ) hc hdr
  have hBS := (z1fMap φ (chRep κ) (chRep κ)).1 hc
  have hSZ : UpperTheory.V.Loc.finiteCocycles φ (chRep κ) ≤ ReciprocityTheory.Gal.Z1 (chRep κ) := fun c h => h.1
  have hBf : Module.Finite E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) := by
    unfold ReciprocityTheory.Gal.B1; infer_instance
  obtain ⟨hS, hSd⟩ := sandwich _ _ _ hBS hSZ (hQ := hfin)
  replace hSd : finrank E ↥(UpperTheory.V.Loc.finiteCocycles φ (chRep κ)) =
    finrank E ↥(finiteCohomology φ (chRep κ)) + finrank E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) := hSd
  have key : w ≠ 0 → ReciprocityTheory.Gal.H0 (chRep κ) = ⊥ ∧ finrank E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) = 1 := by
    intro h0
    obtain ⟨g, hg⟩ := exists_ne_one φ hφ κ w h0 hw
    have hz : ∀ m : E, chRep κ g m - m = 0 → m = 0 := by
      intro m hm
      have h1 : ((κ g : E) - 1) * m = 0 := by
        rw [sub_mul, one_mul]; simpa [chRep] using hm
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd (Units.val_eq_one.1 (sub_eq_zero.1 h)) hg
      · exact h
    refine ⟨?_, ?_⟩
    · rw [eq_bot_iff]
      intro m hm
      exact hz m (sub_eq_zero.2 ((mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm g))
    · unfold ReciprocityTheory.Gal.B1
      rw [LinearMap.finrank_range_of_inj, finrank_self]
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro m hm
      exact hz m (congrFun hm g)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨h0, hB⟩ := key h.ne
    rw [h0, (hfil 0).1 (by omega), finrank_ddr φ _ hdr, finrank_bot, finrank_self] at hdim
    refine ⟨(Submodule.eq_of_le_of_finrank_eq hBS (by omega)).symm, hB⟩
  · obtain ⟨h0, hB⟩ := key h.ne'
    rw [h0, (hfil 0).2 (by omega), finrank_bot, finrank_bot, finrank_self] at hdim
    exact ⟨hS, by omega⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUniqueUnramifiedHomOfFrobeniusValue
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

theorem UpperTheory.exists_unique_unramified_hom_of_frobenius_value :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (v : ℕ), v.Prime → ∀ (A : ValuationSubring Ω), A.valuation (v : Ω) < 1 → ∀ σ : ↥(Dec (F := ℚ) A), Formalism.ConjugateSelfDual.IsFrob (F := ℚ) A v (σ : G ℚ Ω) → ∀ (E : Type) [AddCommGroup E] [Module ℚ_[l] E] [Module.Finite ℚ_[l] E], (∀ e : E, ∃ u : ↥(Dec (F := ℚ) A) → E, QCont l u ∧ (∀ g h, u (g * h) = u g + u h) ∧ (∀ g : ↥(Dec (F := ℚ) A), (g : G ℚ Ω) ∈ Ine (F := ℚ) A → u g = 0) ∧ u σ = e) ∧ ∀ u : ↥(Dec (F := ℚ) A) → E, QCont l u → (∀ g h, u (g * h) = u g + u h) → (∀ g : ↥(Dec (F := ℚ) A), (g : G ℚ Ω) ∈ Ine (F := ℚ) A → u g = 0) → u σ = 0 → u = 0 := by
  intro Ω _ _ _ l _ v hv A hA σ hσ E _ _ _
  haveI : Fact v.Prime := ⟨hv⟩
  obtain ⟨w, hwv, hwA⟩ := GlobalTheory.DecLocal.exists_place_below (p := v) (F := ℚ) A hA
  obtain ⟨j, rfl⟩ := (UpperTheory.V.Loc.decEmb (F := ℚ) (Ω := Ω) (v := v)).1 _ w hwA hwv
  obtain ⟨hemb, hrange, hcomap, -, -, -, hfrob⟩ := UpperTheory.V.Loc.iotaFacts (v := v) j
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalAddGroup E := IsModuleTopology.topologicalAddGroup ℚ_[l] E
  let ρ : Representation ℚ_[l] (Formalism.BasicNotions.Loc.GQ v) E := Representation.trivial ℚ_[l] _ E
  have hρ : ∀ g x, ρ g x = x := fun _ _ => rfl
  have hcont : ContAction ρ := by
    show Continuous fun p : Formalism.BasicNotions.Loc.GQ v × E => ρ p.1 p.2
    simp only [hρ]
    exact continuous_snd
  have hI : ∀ g ∈ Iq v, ρ g = 1 := fun _ _ => rfl
  have hmem : ∀ c : Formalism.BasicNotions.Loc.GQ v → E,
      c ∈ Z1 ρ ↔ Continuous c ∧ ∀ g h, c (g * h) = c g + c h := by
    intro c
    exact Iff.rfl
  have hsurj : ∀ g : ↥(Dec (F := ℚ) (placeJ j)), ∃ x, iota j x = (g : G ℚ Ω) := by
    intro g
    have hg : (g : G ℚ Ω) ∈ (iota j).range := by
      rw [hrange]
      exact g.2
    exact hg
  choose inv hinv using hsurj
  have hinj : Function.Injective (iota j) := hemb.injective
  have hinv_mul : ∀ g h, inv (g * h) = inv g * inv h := by
    intro g h
    apply hinj
    rw [map_mul, hinv, hinv, hinv]
    rfl
  have hinv_cont : Continuous inv := by
    rw [hemb.isInducing.continuous_iff]
    have hfun : (iota j ∘ inv) = fun g : ↥(Dec (F := ℚ) (placeJ j)) => (g : G ℚ Ω) := funext hinv
    rw [hfun]
    exact continuous_subtype_val
  have hmemr : ∀ x, iota j x ∈ Dec (F := ℚ) (placeJ j) := by
    intro x
    rw [← hrange]
    exact ⟨x, rfl⟩
  let ψ : Formalism.BasicNotions.Loc.GQ v → ↥(Dec (F := ℚ) (placeJ j)) := fun x => ⟨iota j x, hmemr x⟩
  have hψ_cont : Continuous ψ := hemb.continuous.subtype_mk _
  have hψ_mul : ∀ x y, ψ (x * y) = ψ x * ψ y := by
    intro x y
    apply Subtype.ext
    simp [ψ]
  have hψinv : ∀ g, ψ (inv g) = g := fun g => Subtype.ext (hinv g)
  obtain ⟨τ, hτ⟩ : (σ : G ℚ Ω) ∈ (iota j).range := by
    rw [hrange]
    exact σ.2
  have hτF : UpperTheory.V.Loc.IsFrob τ := (hfrob τ).2 (hτ ▸ hσ)
  have hinvσ : inv σ = τ := hinj (by rw [hinv, hτ])
  have hIq : ∀ x, x ∈ Iq v ↔ iota j x ∈ Ine (F := ℚ) (placeJ j) := by
    intro x
    rw [← hcomap]
    rfl
  refine ⟨?_, ?_⟩
  · intro e
    obtain ⟨c, ⟨hcZ, hcI, hcσ⟩, -⟩ := UpperTheory.V.Loc.existsUnique_unramified_cocycle_frobenius_value (l := l) (A := ℚ_[l]) ρ hcont hI τ hτF e
    obtain ⟨hcc, hcm⟩ := (hmem c).1 hcZ
    refine ⟨fun g => c (inv g), ?_, ?_, ?_, ?_⟩
    · exact hcc.comp hinv_cont
    · intro g h
      simp only [hinv_mul, hcm]
    · intro g hg
      apply hcI
      rw [hIq, hinv]
      exact hg
    · simp only [hinvσ, hcσ]
  · intro u hu hum huI huσ
    obtain ⟨c0, -, huniq⟩ := UpperTheory.V.Loc.existsUnique_unramified_cocycle_frobenius_value (l := l) (A := ℚ_[l]) ρ hcont hI τ hτF 0
    have hc : (fun x => u (ψ x)) = 0 := by
      have h1 : (fun x => u (ψ x)) = c0 := by
        apply huniq
        refine ⟨(hmem _).2 ⟨hu.comp hψ_cont, ?_⟩, ?_, ?_⟩
        · intro g h
          simp only [hψ_mul, hum]
        · intro g hg
          exact huI _ ((hIq g).1 hg)
        · have : ψ τ = σ := Subtype.ext hτ
          simp only [this, huσ]
      have h2 : (0 : Formalism.BasicNotions.Loc.GQ v → E) = c0 := by
        apply huniq
        refine ⟨(hmem _).2 ⟨continuous_const, ?_⟩, ?_, ?_⟩
        · intro g h
          simp
        · intro g _
          rfl
        · rfl
      rw [h1, h2]
    funext g
    have := congrFun hc (inv g)
    simp only [hψinv] at this
    exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.InertiaFixesOfFrobeniusAnnihilatedMemFilZero
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

private theorem companion {R : Type} [CommRing R] (P : R[X]) (hP : P.Monic) (h0 : IsUnit (P.coeff 0)) :
    ∃ M : Matrix (Fin P.natDegree) (Fin P.natDegree) R, IsUnit M.det ∧
      ∀ i : Fin P.natDegree, P ∣ X ^ ((i : ℕ) + 1) - ∑ j : Fin P.natDegree, C (M i j) * X ^ (j : ℕ) := by
  classical
  let b : Basis (Fin P.natDegree) R (AdjoinRoot P) := (AdjoinRoot.powerBasis' hP).basis
  have hb : ∀ i : Fin P.natDegree, b i = AdjoinRoot.root P ^ (i : ℕ) := fun i =>
    (AdjoinRoot.powerBasis' hP).basis_eq_pow i
  have hr : IsUnit (AdjoinRoot.root P) := by
    have h1 : AdjoinRoot.mk P (X * divX P + C (P.coeff 0)) = 0 := by
      rw [X_mul_divX_add]; exact AdjoinRoot.mk_self
    rw [map_add (f := _), map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h1
    have h2 : IsUnit (AdjoinRoot.root P * AdjoinRoot.mk P (divX P)) := by
      rw [eq_neg_of_add_eq_zero_left h1]
      exact (h0.map (AdjoinRoot.of P)).neg
    exact isUnit_of_mul_isUnit_left h2
  refine ⟨(Algebra.leftMulMatrix b (AdjoinRoot.root P)).transpose, ?_, fun i => ?_⟩
  · rw [Matrix.det_transpose, ← Matrix.isUnit_iff_isUnit_det]
    exact hr.map _
  · rw [← AdjoinRoot.mk_eq_mk]
    have h := b.sum_repr (AdjoinRoot.root P * b i)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, Matrix.transpose_apply,
      Algebra.leftMulMatrix_eq_repr_mul]
    rw [pow_succ', ← hb, ← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h, Algebra.smul_def, hb j]
    rfl

theorem UpperTheory.inertia_fixes_of_frobenius_annihilated_mem_fil_zero :
    ∀ {l : ℕ} [Fact l.Prime] (P : ℤ_[l][X]), P.Monic → IsUnit (P.coeff 0) → ∀ x : Bcr l, aeval ((PP l).φB.toLinearMap : Module.End ℚ_[l] (Bcr l)) (P.map (algebraMap ℤ_[l] ℚ_[l])) x = 0 → (∀ i : ℕ, (PP l).ιB (((PP l).φB)^[i] x) ∈ ((PP l).PD (botExt l)).Fil 0) → ∀ g ∈ Iq l, (PP l).actQ g x = x := by
  intro l _ P hP h0 x hx hF g hg
  classical
  rcases Nat.eq_zero_or_pos P.natDegree with hd | hd
  · rw [hP.natDegree_eq_zero.1 hd, Polynomial.map_one, map_one, Module.End.one_apply] at hx
    rw [hx, map_zero]
  obtain ⟨M, hM, hdiv⟩ := companion P hP h0
  obtain ⟨N, N', hNN, -, hN', hφ, hI⟩ := UpperTheory.exists_algebraic_element_of_algebraicVectorSubspace M hM
  let V : Fin P.natDegree → Bcr l := fun i => ((PP l).φB)^[i] x
  have hpow : ∀ k : ℕ, (((PP l).φB.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ k) x = ((PP l).φB)^[k] x :=
    fun k => by rw [Module.End.pow_apply]; rfl
  have hV : ∀ i, (PP l).φB (V i) =
      ((M.map (fun z => algebraMap ℚ_[l] (Bcr l) (z : ℚ_[l]))).mulVec V) i := fun i => by
    obtain ⟨Q, hQ⟩ := hdiv i
    have h1 := congrArg (fun p : ℤ_[l][X] => aeval ((PP l).φB.toLinearMap : Module.End ℚ_[l] (Bcr l))
      (p.map (algebraMap ℤ_[l] ℚ_[l])) x) hQ
    rw [mul_comm P Q, Polynomial.map_mul, map_mul, Module.End.mul_apply, hx, map_zero] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_sum, Polynomial.map_mul, map_X, map_C,
      map_sub, map_sum, map_mul, map_pow, aeval_X, aeval_C, LinearMap.sub_apply, LinearMap.sum_apply,
      Module.End.mul_apply, hpow, Module.algebraMap_end_apply] at h1
    rw [Function.iterate_succ_apply', sub_eq_zero] at h1
    refine h1.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [Algebra.smul_def]
    rfl
  have hN'N : N' * N = 1 := mul_eq_one_comm.1 hNN
  let Y : Fin P.natDegree → Bcr l := N'.mulVec V
  have hVY : N.mulVec Y = V := by
    simp only [Y, Matrix.mulVec_mulVec, hNN, Matrix.one_mulVec]
  have hφY : ∀ i, (PP l).φB (Y i) = Y i := fun i => by
    have h1 : (PP l).φB (Y i) = ((N'.map (PP l).φB).mulVec ((PP l).φB ∘ V)) i :=
      RingHom.map_mulVec ((PP l).φB : Bcr l →+* Bcr l) N' V i
    have h2 : (PP l).φB ∘ V = (M.map (fun z => algebraMap ℚ_[l] (Bcr l) (z : ℚ_[l]))).mulVec V :=
      funext hV
    have h3 : N'.map (PP l).φB * N.map (PP l).φB = 1 := by
      have := congrArg ((PP l).φB : Bcr l →+* Bcr l).mapMatrix hN'N
      rw [map_mul, map_one] at this
      exact this
    rw [h1, h2, ← hVY, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← hφ, h3,
      Matrix.one_mulVec]
  have hYF : ∀ i, (PP l).ιB (Y i) ∈ ((PP l).PD (botExt l)).Fil 0 := fun i => by
    have h1 : Y i = ∑ j, N' i j * V j := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_mul]
    simpa using ((PP l).PD (botExt l)).Fil_mul 0 0 _ _ (hN' i j) (hF j)
  have hgY : (PP l).actQ g ∘ Y = Y := funext fun i => by
    obtain ⟨c, hc⟩ := ((PP l).PD (botExt l)).fund (Y i) (by rw [(PP l).PD_φ]; exact hφY i)
      (by rw [(PP l).PD_ι]; exact hYF i)
    change (PP l).actQ g (Y i) = Y i
    rw [← hc, AlgEquiv.commutes]
  have h1 : (PP l).actQ g (N.mulVec Y ⟨0, hd⟩) =
      ((N.map ((PP l).actQ g)).mulVec ((PP l).actQ g ∘ Y)) ⟨0, hd⟩ :=
    RingHom.map_mulVec (((PP l).actQ g : Bcr l ≃ₐ[ℚ_[l]] Bcr l) : Bcr l →+* Bcr l) N Y _
  rw [hI g hg, hgY, hVY] at h1
  exact h1
end

