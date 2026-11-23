module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRootNear
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
section
noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct Matrix RestrictedProduct
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem eventually_algebraMap_mem_integers (a : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) a).2

theorem eventually_one_tmul_mem_intLoc (e : E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (1 : Fv F v) ⊗ₜ[F] e ∈ intLoc F E v := by
  have : Algebra.IsAlgebraic ℤ E := IsFractionRing.comap_isAlgebraic_iff.2 (inferInstance : Algebra.IsAlgebraic ℚ E)
  obtain ⟨d, hd, hi⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) e).exists_integral_multiple
  have hd' : (d : F) ≠ 0 := Int.cast_ne_zero.2 hd
  filter_upwards [eventually_algebraMap_mem_integers (d : F)⁻¹] with v hv
  have h := tmul_mem_intLoc hv (⟨d • e, hi⟩ : 𝓞 E)
  convert h using 1
  change _ = _ ⊗ₜ[F] (d • e)
  rw [← Int.cast_smul_eq_zsmul F, ← TensorProduct.smul_tmul, Algebra.smul_def, ← map_mul, mul_inv_cancel₀ hd', map_one]

theorem eventually_map_evalV_mem_intLoc (z : Af F ⊗[F] E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z ∈ intLoc F E v := by
  induction z using TensorProduct.induction_on with
  | zero => exact Eventually.of_forall fun v => by rw [map_zero]; exact zero_mem _
  | add y z hy hz =>
    filter_upwards [hy, hz] with v h h'
    simpa only [map_add] using add_mem h h'
  | tmul a e =>
    filter_upwards [a.2, eventually_one_tmul_mem_intLoc (F := F) e] with v h h'
    have := mul_mem (tmul_mem_intLoc (a := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a) h (1 : 𝓞 E)) h'
    simpa using this

theorem exists_map_evalV_eq (z : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v ⊗[F] E)
    (hz : ∀ᶠ v in cofinite, z v ∈ intLoc F E v) :
    ∃ Z : Af F ⊗[F] E, ∀ v, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) Z = z v := by
  let b := Module.finBasis F E
  let c := RingOfIntegers.basis E
  have h1 : ∀ k, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y ∈ intLoc F E v,
      (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F := fun k => by
    filter_upwards [eventually_all.2 fun j => eventually_algebraMap_mem_integers (b.repr (c j : E) k)] with v hv y hy
    refine intLoc_induction (p := fun y => (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) (fun a ha x => ?_) (by simp) (fun y z h h' => by simpa using add_mem h h')
      (fun y h => by simpa using h) hy
    have e : b.repr (x : E) k = ∑ j, c.repr x j • b.repr (c j : E) k := by
      have e' : (x : E) = ∑ j, c.repr x j • (c j : E) := by
        conv_lhs => rw [← c.sum_repr x]
        simp
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [e', map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, e,
      map_sum, map_zsmul]
    exact mul_mem ha (sum_mem fun j _ => zsmul_mem (hv j) _)
  let A : Fin (Module.finrank F E) → Af F := fun k =>
    ⟨fun v => (Algebra.TensorProduct.basis (Fv F v) b).repr (z v) k, by
      filter_upwards [h1 k, hz] with v h h' using h _ h'⟩
  refine ⟨(Algebra.TensorProduct.basis (Af F) b).equivFun.symm A, fun v => ?_⟩
  apply (Algebra.TensorProduct.basis (Fv F v) b).repr.injective
  ext k
  rw [GlobalTheory.LatticeLocalGlobal.repr_map, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem eventually_one_tmul_mem_latLoc {L : Submodule (𝓞 E) (Fin n → E)}
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (fun i => (1 : Fv F v) ⊗ₜ[F] x i) ∈ latLoc F L v := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact Eventually.of_forall fun v => tmul_mem_latLoc (one_mem _) hx
  | zero => exact Eventually.of_forall fun v => tmul_mem_latLoc (one_mem _) L.zero_mem
  | add x y _ _ hx hy =>
    filter_upwards [hx, hy] with v h h'
    convert add_mem h h' using 1
    funext i
    exact TensorProduct.tmul_add _ _ _
  | smul c x _ hx =>
    filter_upwards [hx, eventually_one_tmul_mem_intLoc (F := F) c] with v h h'
    convert (latLoc F L v).smul_mem ⟨_, h'⟩ h using 1
    funext i
    change _ = (1 : Fv F v) ⊗ₜ[F] c * (1 : Fv F v) ⊗ₜ[F] x i
    simp

theorem eventually_latLoc_le {L L' : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG)
    (hL' : Submodule.span E (L' : Set (Fin n → E)) = ⊤) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, latLoc F L v ≤ latLoc F L' v := by
  obtain ⟨s, rfl⟩ := hL
  filter_upwards [(eventually_all_finset s).2 fun x _ => eventually_one_tmul_mem_latLoc (F := F) hL' x] with v hv y hy
  have h1 : ∀ x ∈ Submodule.span (𝓞 E) (s : Set (Fin n → E)), (fun i => (1 : Fv F v) ⊗ₜ[F] x i) ∈ latLoc F L' v := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hv x hx
    | zero => exact tmul_mem_latLoc (one_mem _) L'.zero_mem
    | add x y _ _ h h' =>
      convert add_mem h h' using 1
      funext i
      exact TensorProduct.tmul_add _ _ _
    | smul c x _ h =>
      convert (latLoc F L' v).smul_mem ⟨_, tmul_mem_intLoc (one_mem _) c⟩ h using 1
      funext i
      change (1 : Fv F v) ⊗ₜ[F] ((c : E) * x i) = (1 : Fv F v) ⊗ₜ[F] (c : E) * (1 : Fv F v) ⊗ₜ[F] x i
      simp
  refine latLoc_induction (p := fun y => y ∈ latLoc F L' v) (fun a ha x hx => ?_) (zero_mem _)
    (fun _ _ => add_mem) (fun _ => neg_mem) hy
  convert (latLoc F L' v).smul_mem ⟨_, tmul_mem_intLoc ha 1⟩ (h1 x hx) using 1
  funext i
  change _ = a ⊗ₜ[F] ((1 : 𝓞 E) : E) * (1 : Fv F v) ⊗ₜ[F] x i
  simp


variable (F) in
theorem eventually_latLoc_eq (L L' : Submodule (𝓞 E) (Fin n → E)) [hL : Submodule.IsFullLattice E L]
    [hL' : Submodule.IsFullLattice E L'] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, latLoc F L v = latLoc F L' v := by
  filter_upwards [eventually_latLoc_le (F := F) (Submodule.IsLattice.fg E L) (Submodule.IsFullLattice.span_eq_top (A := E) (M := L')),
    eventually_latLoc_le (F := F) (Submodule.IsLattice.fg E L') (Submodule.IsFullLattice.span_eq_top (A := E) (M := L))] with v h h' using le_antisymm h h'


theorem isLattice_stdLattice : Submodule.IsFullLattice E (stdLattice E n) := by
  haveI : Submodule.IsLattice E (stdLattice E n) := Submodule.IsLattice.of_fg E (by
    refine Submodule.fg_pi fun _ => ?_
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _)
  refine ⟨eq_top_iff.2 ?_⟩
  intro y _
  rw [← Finset.univ_sum_single y]
  refine sum_mem fun i _ => ?_
  have h1 : (Pi.single i 1 : Fin n → E) ∈ stdLattice E n := fun j _ => ⟨Pi.single (M := fun _ => 𝓞 E) i 1 j, by
      by_cases e : j = i
      · subst e; simp
      · simp [e]⟩
  convert Submodule.smul_mem _ (y i) (Submodule.subset_span h1) using 1
  rw [← Pi.single_smul, smul_eq_mul, mul_one]

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)


omit [NumberField E] in
variable {σ J} in
theorem mem_stabLoc_stdLattice_iff {v : HeightOneSpectrum (𝓞 F)} {k : GLoc σ J v} :
    k ∈ stabLoc σ J (stdLattice E n) v ↔ (∀ i j, (matHom _ σ J k).1 i j ∈ intLoc F E v) ∧
      ∀ i j, (matHom _ σ J k⁻¹).1 i j ∈ intLoc F E v := by
  have h1 : ∀ k ∈ stabLoc σ J (stdLattice E n) v, ∀ i j, (matHom _ σ J k).1 i j ∈ intLoc F E v := fun k hk i j => by
    have := mem_latLoc_stdLattice.1 ((mem_stabLoc.1 hk (Pi.single j 1)).1 (mem_latLoc_stdLattice.2 fun l => by
      by_cases e : l = j
      · subst e; simp
      · simp [e])) i
    simpa using this
  have h2 : ∀ M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), (∀ i j, M i j ∈ intLoc F E v) →
      ∀ y ∈ latLoc F (stdLattice E n) v, M *ᵥ y ∈ latLoc F (stdLattice E n) v := fun M hM y hy =>
    mem_latLoc_stdLattice.2 fun i => show ∑ j, M i j * y j ∈ _ from
      sum_mem fun j _ => mul_mem (hM i j) (mem_latLoc_stdLattice.1 hy j)
  refine ⟨fun hk => ⟨h1 k hk, h1 _ (inv_mem hk)⟩, fun h => mem_stabLoc.2 fun y => ⟨h2 _ h.1 y, fun hy => ?_⟩⟩
  have := h2 _ h.2 _ hy
  rwa [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec] at this

theorem eventually_stabLoc_eq (L L' : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L]
    [Submodule.IsFullLattice E L'] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, stabLoc σ J L v = stabLoc σ J L' v := by
  filter_upwards [eventually_latLoc_eq F L L'] with v h
  rw [stabLoc, stabLoc, h]

variable (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L]

theorem eventually_projFinLoc_mem_stabLoc (g : GFin σ J) :
    ∀ᶠ v in cofinite, projFinLoc σ J v g ∈ stabLoc σ J L v := by
  have := isLattice_stdLattice (E := E) (n := n)
  filter_upwards [eventually_stabLoc_eq σ J L (stdLattice E n),
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_map_evalV_mem_intLoc ((matHom _ σ J g).1 i j),
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_map_evalV_mem_intLoc ((matHom _ σ J g⁻¹).1 i j)]
    with v h h1 h2
  rw [h, mem_stabLoc_stdLattice_iff, ← map_inv]
  exact ⟨h1, h2⟩

theorem eventually_proj_mem_stabLoc (g : GAd σ J) : ∀ᶠ v in cofinite, proj σ J v g ∈ stabLoc σ J L v := by
  simpa using eventually_projFinLoc_mem_stabLoc σ J L (projFin σ J g)

theorem existsUnique_projFinLoc_eq (x : ∀ v, GLoc σ J v) (hx : ∀ᶠ v in cofinite, x v ∈ stabLoc σ J L v) :
    ∃! g : GFin σ J, ∀ v, projFinLoc σ J v g = x v := by
  refine existsUnique_of_exists_of_unique ?_ fun g h hg hh => GFin_ext σ J fun v => (hg v).trans (hh v).symm
  have := isLattice_stdLattice (E := E) (n := n)
  have h0 : ∀ᶠ v in cofinite, (∀ i j, (matHom _ σ J (x v)).1 i j ∈ intLoc F E v) ∧
      ∀ i j, (matHom _ σ J (x v)⁻¹).1 i j ∈ intLoc F E v := by
    filter_upwards [eventually_stabLoc_eq σ J L (stdLattice E n), hx] with v h h'
    rwa [h, mem_stabLoc_stdLattice_iff] at h'
  choose A hA using fun i j => exists_map_evalV_eq (fun v => (matHom _ σ J (x v)).1 i j) (h0.mono fun v h => h.1 i j)
  choose B hB using fun i j =>
    exists_map_evalV_eq (fun v => (matHom _ σ J (x v)⁻¹).1 i j) (h0.mono fun v h => h.2 i j)
  let φ : ∀ v, Af F ⊗[F] E →+* Fv F v ⊗[F] E := fun v =>
    (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)).toRingHom
  have hext : ∀ M N : Matrix (Fin n) (Fin n) (Af F ⊗[F] E), (∀ v, M.map (φ v) = N.map (φ v)) → M = N :=
    fun M N h => Matrix.ext fun i j => GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v => congrFun₂ (h v) i j
  have hA' : ∀ v, (Matrix.of A).map (φ v) = (matHom _ σ J (x v)).1 := fun v => Matrix.ext fun i j => hA i j v
  have hB' : ∀ v, (Matrix.of B).map (φ v) = (matHom _ σ J (x v)⁻¹).1 := fun v => Matrix.ext fun i j => hB i j v
  have hσ : ∀ v z, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (φ v z) = φ v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ z) := fun v z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [φ, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hJ : ∀ v, (JR (Af F) J).map (φ v) = JR (Fv F v) J := fun v => by ext r s; simp [φ, JR, inclR]
  let u : GL (Fin n) (Af F ⊗[F] E) := ⟨Matrix.of A, Matrix.of B,
    hext _ _ fun v => by
      rw [Matrix.map_mul, hA', hB', map_inv, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)],
    hext _ _ fun v => by
      rw [Matrix.map_mul, hA', hB', map_inv, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have hu : u ∈ HR (Af F) σ J := hext _ _ fun v => by
    change (cT _ (Matrix.of A) * _ * Matrix.of A).map _ = _
    rw [Matrix.map_mul, Matrix.map_mul, ← GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map _ _ _ (hσ v), hA', hJ]
    exact (x v).2
  exact ⟨⟨u, hu⟩, fun v => matHom_injective _ σ J (Units.ext (hA' v))⟩

end GlobalTheory.AdelicU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteIdeleCharAtDeterminantRoots
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DetRootChar

theorem circle_hom_factor {G B : Type} [Group G] [CommGroup B] (δ : G →* B) (m : G →* Circle)
    (h : ∀ g, δ g = 1 → m g = 1) : ∃ χ : B →* Circle, ∀ g, χ (δ g) = m g := by
  have hker : δ.rangeRestrict.ker ≤ m.ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    exact h g (congrArg Subtype.val hg)
  obtain ⟨χ, hχ⟩ := GlobalTheory.circle_hom_extend_of_injective δ.range.subtype Subtype.val_injective
    (δ.rangeRestrict.liftOfSurjective δ.rangeRestrict_surjective ⟨m, hker⟩)
  refine ⟨χ, fun g => ?_⟩
  have := hχ (δ.rangeRestrict g)
  rw [MonoidHom.liftOfSurjective, MonoidHom.liftOfRightInverse_comp_apply] at this
  exact this

theorem finPart_sigR (D : D7) (x : AE D) :
    finPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [finPart, sigR]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]

theorem finPart_det (D : D7) (V : HSp D) (g : GA D V) :
    finPart D ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det =
      ((Matrix.GeneralLinearGroup.det (finHom V g) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        Af D.host.F ⊗[D.host.F] D.host.E) := by
  rw [RingHom.map_det]
  rfl

theorem exists_idF_mul (D : D7) (x : (AE D)ˣ)
    (hx : sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) = finPart D (x : AE D)) :
    ∃ (a : (AF D.host.F)ˣ) (y : (AE D)ˣ), finPart D (y : AE D) = 1 ∧ x = y * idF D a := by
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
    intro x
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add (f := _), hσ, add_comm]
  obtain ⟨b, hb⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (Af D.host.F) D.sp.cm.sig htr
    (Units.map (finPart D).toMonoidHom x) hx
  have hb' : algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) (b : Af D.host.F) =
      finPart D (x : AE D) := congrArg Units.val hb
  let a : (AF D.host.F)ˣ :=
    ⟨((1 : Ainf D.host.F), (b : Af D.host.F)), ((1 : Ainf D.host.F), ((b⁻¹ : (Af D.host.F)ˣ) : Af D.host.F)),
      Prod.ext (mul_one _) b.mul_inv, Prod.ext (mul_one _) b.inv_mul⟩
  have ha : Units.map (finPart D).toMonoidHom (idF D a) = Units.map (finPart D).toMonoidHom x := by
    apply Units.ext
    change finPart D ((a : AF D.host.F) ⊗ₜ 1) = finPart D (x : AE D)
    rw [← hb']
    rfl
  refine ⟨a, x * (idF D a)⁻¹, ?_, by simp⟩
  have : Units.map (finPart D).toMonoidHom (x * (idF D a)⁻¹) = 1 := by
    rw [map_mul, map_inv, ha, mul_inv_cancel]
  exact congrArg Units.val this

theorem exists_finite_char : ∀ (D : D7) (V : HSp D) (c : (AE D)ˣ →* Circle), (∀ a, c (idF D a) = 1) → (∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1) → ∃ xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ, ∀ (g : GA D V) (x : (AE D)ˣ), IsDetRoot V g x → ((xi (Matrix.GeneralLinearGroup.det (finHom V g)) : ℂˣ) : ℂ) = ((c x : Circle) : ℂ) := by
  intro D V c hF hinf
  obtain ⟨hex, huniq, -, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D V
  choose r hr using hex
  have hval : ∀ g x, IsDetRoot V g x → c (r g) = c x := by
    intro g x hx
    obtain ⟨a, ha⟩ := huniq g _ _ (hr g) hx
    rw [ha, map_mul, hF, mul_one]
  have hm : ∀ g g', c (r (g * g')) = c (r g) * c (r g') := by
    intro g g'
    rw [hval _ _ (hmul _ _ _ _ (hr g) (hr g')), map_mul]
  let m : GA D V →* Circle := MonoidHom.mk' (fun g => c (r g)) hm
  obtain ⟨χ, hχ⟩ := circle_hom_factor (Matrix.GeneralLinearGroup.det.comp (finHom V)) m (by
    intro g hg
    have hg' : Matrix.GeneralLinearGroup.det (finHom V g) = 1 := hg
    have h1 := congrArg (finPart D) (hr g)
    rw [map_mul, finPart_det, hg', Units.val_one, one_mul, finPart_sigR] at h1
    obtain ⟨a, y, hy, hxy⟩ := exists_idF_mul D (r g) h1.symm
    change c (r g) = 1
    rw [hxy, map_mul, hF, hinf y hy, mul_one])
  refine ⟨Circle.toUnits.comp χ, fun g x hx => ?_⟩
  have : χ (Matrix.GeneralLinearGroup.det (finHom V g)) = c x := (hχ g).trans (hval g x hx)
  rw [MonoidHom.comp_apply, this]
  simp

end GlobalTheory.DetRootChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneRootCongruentOddHostField
section
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.AdLat.RootNear
open scoped TensorProduct

namespace GlobalTheory.OddRoot

theorem finite_root_odd (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hP : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) (n : ℕ)
    (hn : Odd n) (u z : RA F E) (hz : z ∈ intHat F E) (huz : u - 1 = n • z)
    (hu : u * sg (FiniteAdeleRing (𝓞 F) F) c u = 1) :
    ∃ x y : RA F E, x ∈ intHat F E ∧ y ∈ intHat F E ∧ x * y = 1 ∧
      x = u * sg (FiniteAdeleRing (𝓞 F) F) c x ∧ ∃ p ∈ intHat F E, x - 1 = n • p := by
  have hu1 : u = 1 + n * z := by
    rw [nsmul_eq_mul] at huz
    linear_combination huz
  have huO : u ∈ intHat F E := by
    rw [hu1]
    exact add_mem (one_mem _) (mul_mem (natCast_mem _ n) hz)
  obtain ⟨x₁, hx₁, ⟨y₁, hy₁, hxy₁⟩, hr₁⟩ := _root_.GlobalTheory.AdLat.exists_integral_unit_root F E c h2 hc hP u huO hu
  obtain ⟨e, f, hee, hef, hun⟩ :=
    exists_idem (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) n
  obtain ⟨h, hh⟩ : ∃ h, e = 2 * h := by
    obtain ⟨g, hg⟩ := (hun (-1)).exists_right_inv
    obtain ⟨k, hk⟩ := hn
    refine ⟨-(k * e * g), ?_⟩
    rw [hk] at hg
    push_cast at hg
    linear_combination (-e) * hg - (2 * k + 1) * g * hee
  obtain ⟨y₀, hy₀⟩ := (unit_of_integral (inclHat F E) (inclHat_integral F E) (e * n) hun
    (inclHat F E h * ⟨z, hz⟩)).exists_right_inv
  have hse : sg (FiniteAdeleRing (𝓞 F) F) c (inclHat F E e : RA F E) = (inclHat F E e : RA F E) := by
    change sg (FiniteAdeleRing (𝓞 F) F) c (incl F e ⊗ₜ[F] (1 : E)) = incl F e ⊗ₜ[F] (1 : E)
    simp [sg]
  have hee' : (inclHat F E e : RA F E) * inclHat F E e = inclHat F E e := by
    rw [← Subring.coe_mul, ← map_mul, hee]
  have hef' : 1 - (inclHat F E e : RA F E) = n * inclHat F E f := by
    have := congrArg (fun t => (inclHat F E t : RA F E)) hef
    simpa using this
  have hh' : (inclHat F E e : RA F E) = 2 * inclHat F E h := by
    have := congrArg (fun t => (inclHat F E t : RA F E)) hh
    simp only [map_mul, map_ofNat] at this
    exact this
  have hy₀' : (1 + (inclHat F E e : RA F E) * n * (inclHat F E h * z)) * y₀ = 1 := by
    have := congrArg (fun t : intHat F E => (t : RA F E)) hy₀
    simpa using this
  have heO := (inclHat F E e).2
  have hfO := (inclHat F E f).2
  have hhO := (inclHat F E h).2
  have hy₀O := y₀.2
  generalize (inclHat F E e : RA F E) = e' at *
  generalize (inclHat F E f : RA F E) = f' at *
  generalize (inclHat F E h : RA F E) = h' at *
  generalize (y₀ : RA F E) = y' at *
  have hx₁' : x₁ ∈ intHat F E := hx₁
  have hy₁' : y₁ ∈ intHat F E := hy₁
  obtain ⟨w, hw⟩ : ∃ w, w = 1 + e' * n * (h' * z) := ⟨_, rfl⟩
  rw [← hw] at hy₀'
  have hwO : w ∈ intHat F E := by
    rw [hw]
    exact add_mem (one_mem _) (mul_mem (mul_mem heO (natCast_mem _ n)) (mul_mem hhO hz))
  have h2w : 2 * (e' * w) = e' * (1 + u) := by
    rw [hw, hu1]
    linear_combination (-(e' * e' * n * z)) * hh' + (n * z * (e' + 1)) * hee'
  have hr₀ : e' * w = u * sg (FiniteAdeleRing (𝓞 F) F) c (e' * w) := by
    have htwo : IsUnit (2 : RA F E) := by
      have := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (RA F E))
      rwa [map_ofNat] at this
    apply htwo.mul_left_cancel
    have := congrArg (sg (FiniteAdeleRing (𝓞 F) F) c) h2w
    rw [map_mul _ 2, map_ofNat, map_mul _ e' (1 + u), map_add (f := _), map_one, hse] at this
    linear_combination h2w - u * this - e' * hu
  have he1 := sub_mem (one_mem (intHat F E)) heO
  refine ⟨e' * w + (1 - e') * x₁, e' * y' + (1 - e') * y₁, add_mem (mul_mem heO hwO) (mul_mem he1 hx₁'),
    add_mem (mul_mem heO hy₀O) (mul_mem he1 hy₁'), ?_, ?_, e' * e' * (h' * z) + f' * (x₁ - 1),
    add_mem (mul_mem (mul_mem heO heO) (mul_mem hhO hz)) (mul_mem hfO (sub_mem hx₁' (one_mem _))), ?_⟩
  · linear_combination e' * hy₀' + (1 - e') * hxy₁ + (w * y' - w * y₁ - x₁ * y' + x₁ * y₁) * hee'
  · rw [map_add (f := _), map_mul _ (1 - e'), map_sub, map_one, hse]
    linear_combination hr₀ + (1 - e') * hr₁
  · rw [nsmul_eq_mul, hw]
    linear_combination (x₁ - 1) * hef'

end GlobalTheory.OddRoot
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OddRoot
open GlobalTheory.Member

theorem exists_root_odd : ∀ (D : D7) (N : ℕ), Odd N → ∀ u z : (Af D.host.F ⊗[D.host.F] D.host.E), z ∈ intAE D → u - 1 = N • z → u * sigR (Af D.host.F) D.sp.cm.sig u = 1 → ∃ x y : (Af D.host.F ⊗[D.host.F] D.host.E), x ∈ intAE D ∧ y ∈ intAE D ∧ x * y = 1 ∧ x = u * sigR (Af D.host.F) D.sp.cm.sig x ∧ ∃ p ∈ intAE D, x - 1 = N • p := by
  intro D N hN u z hz huz hu
  have hP : ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal →
      ∃ t s : 𝓞 D.host.E, (s : D.host.E) = cF D (t : D.host.E) ∧ t - s ∉ P := by
    intro P hP
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    exact ⟨θ, t, ht, hθ⟩
  have hc : cF D ≠ 1 := by
    intro h
    obtain ⟨P, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
    obtain ⟨t, s, hs, hts⟩ := hP P hM
    rw [h] at hs
    have : s = t := Subtype.ext hs
    rw [this, sub_self] at hts
    exact hts P.zero_mem
  rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at hz ⊢
  exact finite_root_odd D.host.F D.host.E (cF D) D.sp.cm.deg2 hc hP N hN u z hz huz hu

end GlobalTheory.OddRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNthRootIdeleFinitePartOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdeleDiv

theorem exists_infAdele_pow_eq (D : D7) (n : ℕ) (hn : 0 < n)
    (z : InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E) :
    ∃ w : InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E, w ^ n = z := by
  obtain ⟨⟨θ, hθ⟩, H⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  obtain ⟨-, -, hb⟩ := H θ hθ
  choose r hr using fun τ : {τ : D.host.E →+* ℂ // τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD} =>
    IsAlgClosed.exists_pow_nat_eq (θ τ.1 z) hn
  obtain ⟨w, hw⟩ := hb.2 r
  refine ⟨w, hb.1 ?_⟩
  funext τ
  have h1 : θ τ.1 w = r τ := congrFun hw τ
  change θ τ.1 (w ^ n) = θ τ.1 z
  rw [map_pow, h1, hr]

theorem exists_pow_eq_of_finPart_eq_one : ∀ (D : D7) (n : ℕ), 0 < n → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → ∃ y : (AE D)ˣ, y ^ n = x := by
  intro D n hn x hx
  obtain ⟨e, he, -, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  obtain ⟨w, hw⟩ := exists_infAdele_pow_eq D n hn (e (x : AE D)).1
  have h2 : (e (x : AE D)).2 = 1 := (he _).2.trans hx
  have hy : (e.symm (w, 1)) ^ n = (x : AE D) := by
    apply e.injective
    rw [map_pow, RingEquiv.apply_symm_apply]
    exact Prod.ext hw (by rw [h2]; exact one_pow n)
  have hu : IsUnit (e.symm (w, 1)) := (isUnit_pow_iff hn.ne').1 (hy ▸ x.isUnit)
  obtain ⟨y, hy'⟩ := hu
  refine ⟨y, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, hy']
  exact hy

end GlobalTheory.IdeleDiv
end

