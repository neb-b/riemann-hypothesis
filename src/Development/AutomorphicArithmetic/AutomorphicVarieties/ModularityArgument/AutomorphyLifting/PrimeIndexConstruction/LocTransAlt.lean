module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.LocTrans
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UopSum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.Bundle0001

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd Matrix

namespace UpperTheory.V.Z.Win.Birth

private theorem level_zero_eq_maximal_compact {F : Type} [Field F] [NumberField F] (w : Pl F) : K1 w 0 = GlobalTheory.LFun.KGL w (n := 2) := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  have : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _

private theorem scalar_fin {F : Type} [Field F] [NumberField F] (w : Pl F) (x : (w.adicCompletion F)ˣ) :
    finGL F 2 (locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) x)) = GeneralLinearGroup.scalar (Fin 2) (localIdele F w x) := by
  have h := GlobalTheory.CuspRep.finId_det_locGL w (GeneralLinearGroup.scalar (Fin 1) x)
  rw [locGL, GlobalTheory.CuspRep.cornerGL_scalar] at h ⊢
  rw [finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  congr 1
  exact (congrArg (finId F) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans
    (h.trans (congrArg (localIdele F w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))

private theorem hasU_of_map {F : Type} [Field F] [NumberField F] (w : Pl F) {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V}
    {ρ' : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) W} (p : V →ₗ[ℂ] W) (hp : ∀ g y, p (ρ g y) = ρ' g (p y))
    {c : ℕ} {lam : ℂ} {x : V} (h0 : p x ≠ 0) (hx : x ∈ Hi.fixd ρ (K1 w c)) (hU : Uop w ρ c x = lam • x) :
    HasU w ρ' c lam := by
  obtain ⟨N, a, -, h⟩ := Wc.hkReps uopSum F w c
  have hx' : p x ∈ Hi.fixd ρ' (K1 w c) := fun u hu => by rw [← hp, hx u hu]
  refine ⟨p x, h0, hx', ?_⟩
  rw [(h W ρ' _ hx').2]
  have e := (h V ρ x hx).2
  rw [hU] at e
  have e2 := congrArg p e
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, map_sum] at e2
  rw [e2]
  simp only [hp]

open GlobalTheory.PRep GlobalTheory.CuspRep.LocEx in
theorem _root_.UpperTheory.V.Z.Win.Birth.locTrans : LocTrans := by
  intro F _ _ _ π w
  let orb {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
      (κ : Representation ℂ K V) (x : V) : (K →₀ ℂ) →ₗ[ℂ] V := Finsupp.linearCombination ℂ fun k => κ k x

  have orb_comm {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
      (κ : Representation ℂ K V) (T : Module.End ℂ V) (hT : ∀ k x, T (κ k x) = κ k (T x)) (x : V)
      (c : K →₀ ℂ) : orb κ (T x) c = T (orb κ x c) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hT]

  have orb_act {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
      (κ : Representation ℂ K V) (x : V) (k : K) (c : K →₀ ℂ) :
      orb κ x (c.mapDomain (k * ·)) = κ k (orb κ x c) := by
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c c' h h' => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), map_add (f := _), h, h']
    | single a b => simp [orb]

  let annPart {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
      (κ : Representation ℂ K V) (φ : V) : Submodule ℂ V := {
    carrier := {x | ∀ c, orb κ φ c = 0 → orb κ x c = 0}
    add_mem' := fun {x y} hx hy c hc => by
      have : orb κ (x + y) c = orb κ x c + orb κ y c := by
        simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_add (f := _), smul_add, Finset.sum_add_distrib]
      rw [this, hx c hc, hy c hc, add_zero]
    zero_mem' := fun c _ => by simp [orb, Finsupp.linearCombination_apply, Finsupp.sum]
    smul_mem' := fun a x hx c hc => by
      have := orb_comm κ (a • (1 : Module.End ℂ V)) (fun k x => by simp) x c
      simpa [hx c hc] using this }

  have exists_type {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
      (κ : Representation ℂ K V) (φ : V)
      (hφ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => κ k φ))) :
      ∃ (d : ℕ) (ξ : K →* Matrix (Fin d) (Fin d) ℂ), ∀ x ∈ annPart κ φ, ∃ f : (Fin d → ℂ) →ₗ[ℂ] V,
        (∀ k v, f (ξ k *ᵥ v) = κ k (f v)) ∧ x ∈ LinearMap.range f ∧ ∀ v, ∃ c, f v = orb κ x c := by
    have hO : ∀ k, ∀ y ∈ LinearMap.range (orb κ φ), κ k y ∈ LinearMap.range (orb κ φ) := by
      rintro k _ ⟨c, rfl⟩
      exact ⟨_, orb_act κ φ k c⟩
    have : FiniteDimensional ℂ (LinearMap.range (orb κ φ)) := by
      change FiniteDimensional ℂ (LinearMap.range (Finsupp.linearCombination ℂ fun k => κ k φ))
      rwa [Finsupp.range_linearCombination]
    let b := Module.finBasis ℂ (LinearMap.range (orb κ φ))
    obtain ⟨s, hs⟩ := (orb κ φ).rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
    refine ⟨_, (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO), fun x hx => ?_⟩
    have key : ∀ c, orb κ x (s ((orb κ φ).rangeRestrict c)) = orb κ x c := fun c => by
      rw [← sub_eq_zero, ← map_sub]
      refine hx _ ?_
      rw [map_sub, sub_eq_zero]
      exact congrArg Subtype.val (LinearMap.congr_fun hs ((orb κ φ).rangeRestrict c))
    refine ⟨orb κ x ∘ₗ s ∘ₗ b.equivFun.symm.toLinearMap, fun k v => ?_,
      ⟨b.equivFun ((orb κ φ).rangeRestrict (Finsupp.single 1 1)), ?_⟩, fun v => ⟨_, rfl⟩⟩
    · obtain ⟨y, rfl⟩ := b.equivFun.surjective v
      obtain ⟨c, rfl⟩ := (orb κ φ).surjective_rangeRestrict y
      have h1 : (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO) k *ᵥ b.equivFun ((orb κ φ).rangeRestrict c) =
          b.equivFun ((orb κ φ).rangeRestrict (c.mapDomain (k * ·))) := by
        have h2 : (orb κ φ).rangeRestrict (c.mapDomain (k * ·)) = sub κ _ hO k ((orb κ φ).rangeRestrict c) :=
          Subtype.ext (orb_act κ φ k c)
        rw [h2]
        exact LinearMap.toMatrix_mulVec_repr b b _ _
      rw [h1]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key, orb_act]
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key]
      simp [orb]

  have smooth_fin (π : TR.CuspSub F 2) : IsSmooth π.finPart := fun v => by
    convert (π.cusp v.1 v.2).1.level using 1
    ext k
    exact Subtype.ext_iff

  have smooth_loc (π : TR.CuspSub F 2) (w : HeightOneSpectrum (𝓞 F)) : IsSmooth (π.locRep w) := fun v =>
    (smooth_fin π v).preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)

  have cpt_fin (π : TR.CuspSub F 2) (k : TR.Kinf F 2) (g : GL (Fin 2) (Af F)) (y : π.V) :
      π.op (.cpt k) (π.finPart g y) = π.finPart g (π.op (.cpt k) y) := by
    refine Subtype.ext ?_
    change (TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits k)) * TR.rt F 2 (finGL F 2 g)) y.1 =
      (TR.rt F 2 (finGL F 2 g) * TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits k))) y.1
    rw [← map_mul, ← map_mul, TR.infGL_comm]

  have fin_loc (π : TR.CuspSub F 2) (w : HeightOneSpectrum (𝓞 F)) {k : GL (Fin 2) (Af F)}
      (hk : GeneralLinearGroup.map (pLoc F w) k = 1) (g : GL (Fin 2) (w.adicCompletion F)) (y : π.V) :
      π.finPart k (π.locRep w g y) = π.locRep w g (π.finPart k y) := by
    simp only [TR.CuspSub.locRep, MonoidHom.comp_apply]
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul, GlobalTheory.CuspRep.LocUniq.comm_locGL w hk]

  have bot_or_top (π : TR.CuspSub F 2) (w : HeightOneSpectrum (𝓞 F)) (W : Submodule ℂ π.V)
      (h1 : ∀ g, ∀ x ∈ W, π.locRep w g x ∈ W)
      (h2 : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.locRep w g x) = π.locRep w g (T x)) → ∀ x ∈ W, T x ∈ W) :
      W = ⊥ ∨ W = ⊤ := by
    have hi := Submodule.map_injective_of_injective π.V.injective_subtype
    have hop : ∀ o, ∀ x ∈ W, π.op o x ∈ W := fun o x hx => by
      cases o with
      | fin k =>
        have h3 := h1 (GeneralLinearGroup.map (pLoc F w) k) _ (h2
          (π.finPart ((locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ * k))
          (fin_loc π w (map_pLoc_inv_mul w k)) x hx)
        rwa [TR.CuspSub.locRep, MonoidHom.comp_apply, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left] at h3
      | cpt k => exact h2 _ (fun g y => cpt_fin π k _ y) x hx
      | lie X => exact h2 _ (fun g y => Subtype.ext (LinearMap.congr_fun (TR.lie_rt_fin X (locGL F 2 w g)) y.1)) x hx
    rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
      rintro o _ ⟨x, hx, rfl⟩
      exact ⟨_, hop o x hx, rfl⟩) with h | h
    · exact Or.inl (hi (h.trans (Submodule.map_bot _).symm))
    · exact Or.inr (hi (h.trans (Submodule.map_subtype_top _).symm))

  have isotypic (π : TR.CuspSub F 2) (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F)))
      (h : π.IsLocComp w σ) : LocIsotypic π.finPart w σ := by
    refine ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne_bot, ?_⟩
    refine (bot_or_top π w _ (fun g x hx => ?_) (fun T hT x hx => ?_)).resolve_left fun e => ?_
    · refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap (π.locRep w g) _) fun f => ?_) hx)
      rintro _ ⟨v, rfl⟩
      exact Submodule.mem_iSup_of_mem f ⟨σ.ρ g v, f.2 g v⟩
    · refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap T _) fun f => ?_) hx)
      rintro _ ⟨v, rfl⟩
      exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by
        rw [LinearMap.comp_apply, f.2]; exact hT g _⟩ ⟨v, rfl⟩
    · obtain ⟨f, h0, hf⟩ := h
      exact h0 (LinearMap.range_eq_bot.1 ((iSup_eq_bot.1 e) ⟨f, hf⟩))

  let cptPart (π : TR.CuspSub F 2) : Representation ℂ (TR.Kinf F 2) π.V :=
    sub (TR.cptRep F 2) π.V fun k => π.stable (.cpt k)

  have exists_comp : ∃ σ, π.IsLocComp w σ := by
    obtain ⟨φ₀, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
    set φ : π.V := ⟨φ₀, hφ⟩
    have h0' : φ ≠ 0 := fun e => h0 (congrArg Subtype.val e)
    set L := stab π.finPart φ
    have hL : IsOpen (L : Set (GL (Fin 2) (Af F))) := smooth_fin π _
    obtain ⟨K, ho, hc, hK⟩ := exists_compact_open w _ hL
    have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptPart π k φ)) := by
      have := (π.cusp φ₀ hφ).1.kfin
      refine FiniteDimensional.of_injective ((π.V.subtype ∘ₗ Submodule.subtype _).codRestrict
        (Submodule.span ℂ (Set.range fun k => TR.cptRep F 2 k φ₀)) fun v => ?_)
        fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
      refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap π.V.subtype _)).2 ?_ v.2)
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨k, rfl⟩
    obtain ⟨d, ξ, hξ⟩ := exists_type (cptPart π) φ hfd
    have hcomm : ∀ g k x, π.finPart g (cptPart π k x) = cptPart π k (π.finPart g x) := fun g k x => (cpt_fin π k g x).symm
    let U : Submodule ℂ π.V := annPart (cptPart π) φ ⊓
      fixed π.finPart (L ⊓ (GeneralLinearGroup.map (n := Fin 2) (pLoc F w)).ker)
    obtain ⟨σ, hσ, -⟩ := exists_irred (smooth_loc π w) ho (fun W hW e => by
        rcases bot_or_top π w (nullPart (π.locRep w) K) (fun g x hx => nullPart_act _ K g hx)
          (fun T hT x hx => nullPart_comm _ K T hT hx) with h2 | h2
        · exact le_bot_iff.1 (h2 ▸ le_nullPart (smooth_loc π w) hc W hW e)
        · exact absurd (eq_zero_of_mem_nullPart (smooth_loc π w) hc (mem_fix.2 hK) (h2 ▸ Submodule.mem_top)) h0')
      U (fun g x hx => ⟨fun c hc => by
          rw [TR.CuspSub.locRep, MonoidHom.comp_apply, orb_comm _ _ (hcomm _), hx.1 c hc, map_zero],
        mem_fix.2 fun k hk => by rw [fin_loc π w hk.2, mem_fix.1 hx.2 k hk]⟩)
      ((Submodule.ne_bot_iff _).2 ⟨φ, ⟨fun _ hc => hc, mem_fix.2 fun k hk => hk.1⟩, h0'⟩) (fun K' hK' => by
        obtain ⟨W, hW, hWf⟩ := admissibleReal F 2 π (L ⊓ (K' ⊓ L.comap (locGL F 2 w)).comap (GeneralLinearGroup.map (pLoc F w)))
          (hL.inter ((hK'.inter (hL.preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w))).preimage
            (continuous_map_pLoc w))) d ξ
        refine Submodule.finiteDimensional_of_le (S₂ := W) fun x hx => ?_
        obtain ⟨f, hf, hx1, hf2⟩ := hξ x hx.1.1
        refine hWf f hf (fun k hk v => ?_) hx1
        have h1 := mem_fix.1 hx.1.2 _ ⟨L.mul_mem (L.inv_mem hk.2.2) hk.1, map_pLoc_inv_mul w k⟩
        have h2 := mem_fix.1 hx.2 _ hk.2.1
        have h3 : π.finPart k x = x := by
          rw [← mul_inv_cancel_left (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) k, map_mul,
            mul_apply_eq_comp, h1]
          exact h2
        obtain ⟨c, hc⟩ := hf2 v
        rw [hc, ← orb_comm _ _ (hcomm k), h3])
    exact ⟨σ, hσ⟩
  refine ⟨fun ⟨x, hx0, hx⟩ => ?_, fun σ hσ => ⟨fun c lam ⟨x, hx0, hx, hU⟩ => ?_, fun ω hω z v => ?_⟩⟩
  · obtain ⟨σ, hσ⟩ := exists_comp
    have hi := isotypic π w σ hσ
    have hxK : x ∈ GlobalTheory.PRep.fixed (π.locRep w) (GlobalTheory.LFun.KGL w (n := 2)) :=
      GlobalTheory.LGrp.mem_fixed.2 (fun k hk => hx k (level_zero_eq_maximal_compact w ▸ hk))
    let maps := {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}
    obtain ⟨y, hy0, hy⟩ := GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.locRep w) σ.ρ σ.irred
      (fun f : maps => f.1) (fun f => f.2) _ x hx0 (GlobalTheory.LGrp.mem_fixed.1 hxK)
      (hi.2 ▸ Submodule.mem_top)
    obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred
      ((Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩)
    refine ⟨B, ⟨(Submodule.ne_bot_iff _).2 ⟨x, hxK, hx0⟩, fun v hv h0 => ?_⟩⟩
    exact GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup σ.irred hB
      (fun f : maps => f.1) (fun f => f.2) (hi.2 ▸ Submodule.mem_top) hv h0
  · classical
    let τ := π.locRep w
    let maps := {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = τ g (f v)}
    have htop : ⨆ f : maps, LinearMap.range f.1 = ⊤ := (isotypic π w σ hσ).2
    let Fmap (f : maps) : σ.ρ.asModule →ₗ[MonoidAlgebra ℂ _] τ.asModule :=
      Representation.IntertwiningMap.equivLinearMapAsModule σ.ρ τ
        ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩
    let Φ := Finsupp.lsum ℕ Fmap
    have hΦ : Function.Surjective Φ := fun y => by
      obtain ⟨v, rfl⟩ := τ.asModuleEquiv.symm.surjective y
      have hv : v ∈ ⨆ f : maps, LinearMap.range f.1 := htop ▸ Submodule.mem_top
      refine Submodule.iSup_induction _ (motive := fun v => ∃ z, Φ z = τ.asModuleEquiv.symm v) hv ?_ ?_ ?_
      · rintro f _ ⟨v, rfl⟩
        exact ⟨Finsupp.single f (σ.ρ.asModuleEquiv.symm v), Finsupp.lsum_single _ _ _ _⟩
      · exact ⟨0, (map_zero Φ).trans (map_zero τ.asModuleEquiv.symm).symm⟩
      · rintro a b ⟨z, hz⟩ ⟨z', hz'⟩
        exact ⟨z + z', by rw [map_add Φ, hz, hz', map_add τ.asModuleEquiv.symm]⟩
    have := σ.irred
    have := IsSemisimpleModule.of_surjective Φ hΦ
    obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property Φ hΦ (LinearMap.id : τ.asModule →ₗ[MonoidAlgebra ℂ _] τ.asModule)
    let x' := τ.asModuleEquiv.symm x
    have hsx : s x' ≠ 0 := by
      intro e
      have h := LinearMap.congr_fun hs x'
      change Φ (s x') = x' at h
      rw [e, map_zero] at h
      exact (map_ne_zero_iff _ τ.asModuleEquiv.symm.injective).2 hx0 h.symm
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hsx
    let p := (Representation.IntertwiningMap.equivLinearMapAsModule τ σ.ρ).symm (Finsupp.lapply i ∘ₗ s)
    exact hasU_of_map w p.toLinearMap (fun g v => p.isIntertwining _ _ g v) hi hx hU
  · obtain ⟨f, h0, hf⟩ := hσ
    have hinj : LinearMap.ker f = ⊥ := ((isIrreducible_iff σ.ρ).1 σ.irred).2 _ (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hf, hv, map_zero]) |>.resolve_right fun e => h0 (LinearMap.ker_eq_top.1 e)
    refine LinearMap.ker_eq_bot.1 hinj ?_
    rw [hf, map_smul]
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    change (f v).1.1 (g * finGL F 2 (locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) z))) = ((ω.loc w z : ℂˣ) : ℂ) * (f v).1.1 g
    rw [scalar_fin, ← GlobalTheory.CuspRep.scalar_comm, hω _ _ (f v).2]
    rfl

end UpperTheory.V.Z.Win.Birth
