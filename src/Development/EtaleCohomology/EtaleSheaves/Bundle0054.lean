module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0050
public import Development.EtaleCohomology.EtaleSheaves.Bundle0045
public import Development.EtaleCohomology.EtaleSheaves.Bundle0021
public import Development.EtaleCohomology.EtaleSheaves.AlgebraicIntegralClosure.AicLoc
public import Development.EtaleCohomology.EtaleSheaves.Bundle0043
public import Development.EtaleCohomology.EtaleSheaves.Bundle0048

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.AicOfIsLocalization
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial Opposite

namespace LateralTheory.E.LocPf

theorem root_mem_range {A K : Type} [CommRing A] [CommRing K] [IsDomain K] (hA : GlobalTheory.EtC.AIC A) (φ : A →+* K) :
    ∀ (n : ℕ) (p : A[X]), p.natDegree = n → p.Monic → ∀ a : K, p.eval₂ φ a = 0 → ∃ b, φ b = a := by
  intro n
  induction n with
  | zero =>
    intro p hn hp a ha
    rw [eq_one_of_monic_natDegree_zero hp hn, eval₂_one] at ha
    exact absurd ha one_ne_zero
  | succ n ih =>
    intro p hn hp a ha
    have : Nontrivial A := by
      by_contra hnt; rw [not_nontrivial_iff_subsingleton] at hnt
      rw [Subsingleton.elim p 0] at hn; simp at hn
    obtain ⟨b, hb⟩ := hA p hp (by omega)
    have e := (mul_divByMonic_eq_iff_isRoot (p := p) (a := b)).mpr hb
    have hq : (p /ₘ (X - C b)).Monic := Monic.of_mul_monic_left (monic_X_sub_C b) (by rw [e]; exact hp)
    have hdeg : (p /ₘ (X - C b)).natDegree = n := by
      have := (monic_X_sub_C b).natDegree_mul hq
      rw [e, natDegree_X_sub_C] at this; omega
    rw [← e, eval₂_mul, eval₂_sub, eval₂_X, eval₂_C] at ha
    rcases mul_eq_zero.mp ha with h | h
    · exact ⟨b, (sub_eq_zero.mp h).symm⟩
    · exact ih _ hdeg hq a h

theorem aic_of_isLocalization {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (M : Submonoid A)
    [IsLocalization M B] (hA : GlobalTheory.EtC.AIC A) : GlobalTheory.EtC.AIC B := by
  intro p hp hd
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite M (fun i : Fin (p.natDegree + 1) => p.coeff i)
  set t := algebraMap A B b with ht
  have hlift : p.scaleRoots t ∈ lifts (algebraMap A B) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    rcases lt_trichotomy i p.natDegree with h | h | h
    · obtain ⟨c, hc⟩ := hb ⟨i, by omega⟩
      refine ⟨c * (b : A) ^ (p.natDegree - i - 1), ?_⟩
      rw [map_mul, map_pow, hc, Algebra.smul_def, ← ht]
      rw [show t ^ (p.natDegree - i) = t * t ^ (p.natDegree - i - 1) by rw [← pow_succ']; congr 1; omega]
      ring
    · subst h; rw [hp.coeff_natDegree]; exact ⟨1, by simp⟩
    · rw [coeff_eq_zero_of_natDegree_lt h]; exact ⟨0, by simp⟩
  obtain ⟨q, hqm, hqd, hq⟩ := lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff t).mpr hp)
  obtain ⟨c, hc⟩ := hA q hq (by rw [hqd, natDegree_scaleRoots]; exact hd)
  obtain ⟨u, hu⟩ := (IsLocalization.map_units B b).exists_right_inv
  refine ⟨u * algebraMap A B c, ?_⟩
  have h1 : p = (p.scaleRoots t).scaleRoots u := by
    rw [← scaleRoots_mul, ht, hu, scaleRoots_one]
  have h2 : (p.scaleRoots t).eval (algebraMap A B c) = 0 := by
    rw [← hqm, Polynomial.eval_map, eval₂_at_apply, hc, map_zero]
  conv_lhs => rw [h1]
  rw [scaleRoots_eval_mul, h2, mul_zero]

theorem germ_comp (Z : Scheme.{0}) {W U : Z.Opens} (i : W ≤ U) (x : Z) (hx : x ∈ W) :
    (Z.presheaf.germ W x hx).hom.comp (Z.presheaf.map (homOfLE i).op).hom = (Z.presheaf.germ U x (i hx)).hom := by
  ext s; simp

theorem exists_small (Z : Scheme.{0}) (h : ∀ z : Z, ∃ U : Z.Opens, IsAffineOpen U ∧ z ∈ U ∧ GlobalTheory.EtC.AIC Γ(Z, U))
    (U : Z.Opens) (z : Z) (hz : z ∈ U) : ∃ W : Z.Opens, W ≤ U ∧ z ∈ W ∧ GlobalTheory.EtC.AIC Γ(Z, W) := by
  obtain ⟨V, hV, hzV, hA⟩ := h z
  obtain ⟨f, hle, hzf⟩ := hV.exists_basicOpen_le (V := U) ⟨z, hz⟩ hzV
  have := hV.isLocalization_basicOpen f
  exact ⟨Z.basicOpen f, hle, hzf, aic_of_isLocalization (Submonoid.powers f) hA⟩

theorem loc : LateralTheory.E.NormACPf.Loc := by
  intro Z hZ h U hU ⟨z0, hz0⟩ p hp hd
  set η := genericPoint Z
  have hη : ∀ W : Z.Opens, (W : Set Z).Nonempty → η ∈ W := fun W hW =>
    ((genericPoint_spec Z).mem_open_set_iff W.isOpen).mpr (by simpa using hW)
  have hηU : η ∈ U := hη U ⟨z0, hz0⟩
  choose W hWU hzW hWA using fun z : U => exists_small Z h U z.1 z.2
  have hηW : ∀ z : U, η ∈ W z := fun z => hη _ ⟨z.1, hzW z⟩
  let gU := (Z.presheaf.germ U η hηU).hom
  let res := fun z : U => (Z.presheaf.map (homOfLE (hWU z)).op).hom
  have hdom : ∀ z : U, Nontrivial Γ(Z, W z) := fun z => by
    have : Nonempty (W z) := ⟨⟨z.1, hzW z⟩⟩; infer_instance
  let z0' : U := ⟨z0, hz0⟩
  obtain ⟨b0, hb0⟩ := hWA z0' (p.map (res z0')) (hp.map _) (by rw [hp.natDegree_map]; exact hd)
  set a := Z.presheaf.germ (W z0') η (hηW z0') b0 with ha_def
  have hroot : p.eval₂ gU a = 0 := by
    have := congrArg (Z.presheaf.germ (W z0') η (hηW z0')).hom hb0
    rw [Polynomial.eval_map, hom_eval₂, germ_comp, map_zero] at this
    exact this
  have hc : ∀ z : U, ∃ c, Z.presheaf.germ (W z) η (hηW z) c = a := by
    intro z
    refine root_mem_range (hWA z) (Z.presheaf.germ (W z) η (hηW z)).hom _ (p.map (res z)) rfl (hp.map _) a ?_
    rw [eval₂_map, germ_comp]; exact hroot
  choose c hcz using hc
  obtain ⟨s1, hs1, -⟩ := TopCat.Sheaf.existsUnique_gluing' Z.sheaf W U (fun z => homOfLE (hWU z))
    (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hzW _⟩) c (by
      intro i j
      apply germ_injective_of_isIntegral Z (U := W i ⊓ W j) η (show η ∈ W i ⊓ W j from ⟨hηW i, hηW j⟩)
      change (Z.presheaf.germ _ η _) (Z.presheaf.map _ (c i)) = (Z.presheaf.germ _ η _) (Z.presheaf.map _ (c j))
      rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hcz, hcz])
  obtain ⟨s, hs⟩ : ∃ s : Γ(Z, U), ∀ i, Z.presheaf.map (homOfLE (hWU i)).op s = c i := ⟨s1, hs1⟩
  have hsa : gU s = a := by
    have := hs z0'
    rw [← hcz z0', ← this]
    change _ = (Z.presheaf.germ _ η _) (Z.presheaf.map _ s)
    rw [TopCat.Presheaf.germ_res_apply]
  refine ⟨s, germ_injective_of_isIntegral Z η hηU ?_⟩
  change gU (p.eval s) = gU 0
  rw [map_zero, ← eval₂_at_apply, hsa, hroot]

end LateralTheory.E.LocPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.AlgebraicIntegralClosure
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Polynomial LateralTheory.E.t_E2Cut LateralTheory.E.AICOpenPf

namespace LateralTheory.E.BaseAICPf

theorem aic_of_local {Z : Scheme.{0}} [IsIntegral Z]
    (hloc : ∀ (W : Z.Opens) (y : Z), y ∈ W → ∃ U : Z.Opens, y ∈ U ∧ U ≤ W ∧ AIC Γ(Z, U))
    (W : Z.Opens) (hW : (W : Set Z).Nonempty) : AIC Γ(Z, W) := by
  intro p hm hd
  have : Nonempty W := ⟨⟨_, hW.some_mem⟩⟩
  have hcov : ∀ x : W, ∃ U : Z.Opens, (x : Z) ∈ U ∧ U ≤ W ∧ AIC Γ(Z, U) := fun x => hloc W x x.2
  choose U hxU hUW hUa using hcov
  have hne : ∀ x : W, Nonempty (U x) := fun x => ⟨⟨_, hxU x⟩⟩
  let ψ := Z.germToFunctionField W
  have hroot : ∀ x : W, ∃ β : Z.functionField, (p.map ψ.hom).eval β = 0 := by
    intro x
    have := hne x
    have hA : AIC Γ(Z, U x) := hUa x
    let ρ := (Z.presheaf.map (homOfLE (hUW x)).op).hom
    obtain ⟨r, hr⟩ := hA (p.map ρ) (hm.map ρ) (by rw [hm.natDegree_map]; exact hd)
    refine ⟨Z.germToFunctionField (U x) r, ?_⟩
    rw [← gtf_res_hom (homOfLE (hUW x)), ← Polynomial.map_map, Polynomial.eval_map_apply, hr, map_zero]
  obtain ⟨β, hβ⟩ := hroot ⟨_, hW.some_mem⟩
  have hsec : ∀ x : W, ∃ t : Γ(Z, U x), Z.germToFunctionField (U x) t = β := by
    intro x
    have := hne x
    have hA : AIC Γ(Z, U x) := hUa x
    let ρ := (Z.presheaf.map (homOfLE (hUW x)).op).hom
    exact roots_in (Z.germToFunctionField (U x)).hom hA _ (p.map ρ) rfl (hm.map ρ) β
      (by rw [Polynomial.map_map, gtf_res_hom]; exact hβ)
  choose sf hsf using hsec
  have hcompat : TopCat.Presheaf.IsCompatible Z.sheaf.1 U sf := by
    intro i j
    have := hne i; have := hne j
    have hij : ((U i ⊓ U j : Z.Opens) : Set Z).Nonempty :=
      nonempty_preirreducible_inter (U i).isOpen (U j).isOpen ⟨_, hxU i⟩ ⟨_, hxU j⟩
    have : Nonempty (U i ⊓ U j : Z.Opens) := ⟨⟨_, hij.some_mem⟩⟩
    apply Z.germToFunctionField_injective (U i ⊓ U j)
    change Z.germToFunctionField _ (Z.presheaf.map _ (sf i)) = Z.germToFunctionField _ (Z.presheaf.map _ (sf j))
    rw [gtf_res, gtf_res, hsf, hsf]
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (U := U) (V := W) (iUV := fun x => homOfLE (hUW x))
    (hcover := fun y hy => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxU _⟩) (sf := sf) (h := hcompat)
  have hsβ : ψ s = β := by
    have h0 := hs ⟨_, hW.some_mem⟩
    have := hne ⟨_, hW.some_mem⟩
    rw [← hsf ⟨_, hW.some_mem⟩, ← gtf_res (homOfLE (hUW ⟨_, hW.some_mem⟩)) s]
    exact congrArg _ h0
  obtain ⟨t, ht⟩ : ∃ t : Γ(Z, W), ψ t = β := ⟨s, hsβ⟩
  refine ⟨t, Z.germToFunctionField_injective W ?_⟩
  rw [map_zero]
  have key : ψ.hom (p.eval t) = (p.map ψ.hom).eval (ψ.hom t) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  change ψ.hom (p.eval t) = 0
  rw [key]; change (p.map ψ.hom).eval (ψ t) = 0
  rw [ht]; exact hβ

def BaseInt : Prop := ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S → ∀ x : S, IsIntegral (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0})

def BaseLoc : Prop := ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S → ∀ x : S, ∀ (W : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens)
  (y : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0})), y ∈ W →
  ∃ U : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens, y ∈ U ∧ U ≤ W ∧
    AIC Γ((Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}), U)

def BaseLocLoc : Prop := ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S → ∀ x : S, ∀ (W : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens)
  (y : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0})), y ∈ W →
  ∃ U : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens, y ∈ U ∧ U ≤ W ∧
    ∃ V : Z.Opens, IsAffineOpen V ∧ (V : Set Z).Nonempty ∧
    ∃ f : Γ(Z, V) →+* Γ((Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}), U), ∃ M : Submonoid Γ(Z, V),
      @IsLocalization _ _ M _ _ f.toAlgebra

theorem BaseLoc_of (h : BaseLocLoc) : BaseLoc := by
  intro Z S c _ _ _ hZ hS x W y hy
  obtain ⟨U, hyU, hUW, V, hV, hne, f, M, hM⟩ := h c hZ hS x W y hy
  letI := f.toAlgebra
  exact ⟨U, hyU, hUW, LateralTheory.E.BaseAICPf.Loc.aic_loc M (hZ.2 V hV hne)⟩

theorem BaseAIC_of (h1 : BaseInt) (h2 : BaseLoc) : LateralTheory.E.FibreEqvPf.BaseAIC := by
  intro Z S c _ _ _ hZ hS x
  have : IsIntegral (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}) := h1 c hZ hS x
  exact ⟨this, fun U _ hne => aic_of_local (h2 c hZ hS x) U hne⟩

end LateralTheory.E.BaseAICPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.AugBijPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.AugBijPf

def Sep : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (T : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (g : ∀ i, V i ⟶ T),
  (∀ i, Etale (g i)) → (∀ t : T, ∃ i, ∃ v : V i, (g i).base v = t) →
  ∀ x y : Sec F T, (∀ i, Sec.res (g i) x = Sec.res (g i) y) → x = y

def Glue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (T : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (g : ∀ i, V i ⟶ T),
  (∀ i, Etale (g i)) → (∀ t : T, ∃ i, ∃ v : V i, (g i).base v = t) →
  ∀ x : ∀ i, Sec F (V i), (∀ i j, Sec.res (pullback.fst (g i) (g j)) (x i) = Sec.res (pullback.snd (g i) (g j)) (x j)) →
  ∃ y : Sec F T, ∀ i, Sec.res (g i) y = x i

def LocSurj : Prop := ∀ (q : ℕ) (φ : ∀ T : Scheme.{0}, Sec (tw q 0) T →+ LocallyConstant T (ZMod q)),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U), φ V (Sec.res g x) = (φ U x).comap g.base.hom) →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), φ U (twGen 0 ζ) = 1) →
  ∀ T : Scheme.{0}, IsUnit (q : Γ(T, ⊤)) → ∀ f : LocallyConstant T (ZMod q),
  ∃ (ι : Type) (V : ι → Scheme.{0}) (g : ∀ i, V i ⟶ T), (∀ i, Etale (g i)) ∧ (∀ t : T, ∃ i, ∃ v : V i, (g i).base v = t) ∧
    ∀ i, ∃ y : Sec (tw q 0) (V i), φ (V i) y = f.comap (g i).base.hom

def LocInj : Prop := ∀ (q : ℕ) (φ : ∀ T : Scheme.{0}, Sec (tw q 0) T →+ LocallyConstant T (ZMod q)),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U), φ V (Sec.res g x) = (φ U x).comap g.base.hom) →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), φ U (twGen 0 ζ) = 1) →
  ∀ T : Scheme.{0}, IsUnit (q : Γ(T, ⊤)) → ∀ x : Sec (tw q 0) T, φ T x = 0 →
  ∃ (ι : Type) (V : ι → Scheme.{0}) (g : ∀ i, V i ⟶ T), (∀ i, Etale (g i)) ∧ (∀ t : T, ∃ i, ∃ v : V i, (g i).base v = t) ∧
    ∀ i, Sec.res (g i) x = 0

theorem unit_res {q : ℕ} {V T : Scheme.{0}} (g : V ⟶ T) (h : IsUnit (q : Γ(T, ⊤))) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using h.map g.appTop.hom

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res f (Sec.res g x) = Sec.res (f ≫ g) x := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem sheafFor {R : Type} [CommRing R] (F : Shv R) {T : Scheme.{0}} {ι : Type} {V : ι → Scheme.{0}} (g : ∀ i, V i ⟶ T)
    (he : ∀ i, Etale (g i)) (hs : ∀ t : T, ∃ i, ∃ v : V i, (g i).base v = t) :
    (Presieve.ofArrows V g).IsSheafFor (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) := by
  have h1 : Presheaf.IsSheaf Scheme.etaleTopology.{0} (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property
  have h2 := (isSheaf_iff_isSheaf_of_type _ _).1 h1
  refine Presieve.IsSheaf.isSheafFor_of_mem_precoverage (J := Scheme.precoverage @Etale) h2 ?_
  exact (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun x => by obtain ⟨i, v, hv⟩ := hs x; exact ⟨i, v, hv⟩, he⟩

theorem Sep_holds : Sep := by
  intro R _ F T ι V g he hs x y hxy
  have h := (Presieve.isSheafFor_arrows_iff_pullbacks _ _).1 (sheafFor F g he hs) (fun i => Sec.res (g i) y) (by
    intro i j
    change Sec.res _ (Sec.res _ y) = Sec.res _ (Sec.res _ y)
    rw [res_comp, res_comp, pullback.condition])
  exact h.unique (fun i => hxy i) (fun i => rfl)

theorem Glue_holds : Glue := by
  intro R _ F T ι V g he hs x hx
  obtain ⟨y, hy, -⟩ := (Presieve.isSheafFor_arrows_iff_pullbacks _ _).1 (sheafFor F g he hs) x hx
  exact ⟨y, hy⟩

def Root : Prop := ∀ (q : ℕ) (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
  ∃ (W : Scheme.{0}) (h : W ⟶ U), Etale h ∧ (∀ u : U, ∃ w : W, h.base w = u) ∧ Nonempty (Prim q Γ(W, ⊤))

theorem LocSurj_of (hR : Root) : LocSurj := by
  intro q φ hnat hgen T hT f
  let O : ZMod q → T.Opens := fun c => ⟨{t | f t = c}, f.isLocallyConstant.isOpen_fiber c⟩
  choose W h he hs hζ using fun c => hR q (O c) (unit_res (O c).ι hT)
  refine ⟨ZMod q, W, fun c => h c ≫ (O c).ι, fun c => by haveI := he c; infer_instance, ?_, ?_⟩
  · intro t
    have ht : t ∈ Set.range (O (f t)).ι.base := by rw [Scheme.Opens.range_ι]; exact (rfl : f t = f t)
    obtain ⟨u, hu⟩ := ht
    obtain ⟨w, hw⟩ := hs (f t) u
    exact ⟨f t, w, by rw [Scheme.Hom.comp_apply, hw, hu]⟩
  · intro c
    refine ⟨((c.cast : ℤ)) • twGen 0 (hζ c).some, ?_⟩
    rw [map_zsmul, hgen]
    ext w
    have hm : ((O c).ι.base (h c w)) ∈ O c := by
      have hr : ((O c).ι.base (h c w)) ∈ Set.range (O c).ι.base := ⟨_, rfl⟩
      rw [Scheme.Opens.range_ι] at hr; exact hr
    have hm' : f ((O c).ι.base (h c w)) = c := hm
    have e1 : ((c.cast : ℤ) • (1 : LocallyConstant (W c) (ZMod q))) w = c := by
      change (c.cast : ℤ) • (1 : ZMod q) = c
      rw [zsmul_eq_mul, mul_one, ZMod.intCast_cast, ZMod.cast_id', id_eq]
    rw [e1, LocallyConstant.coe_comap, Function.comp_apply]
    erw [Scheme.Hom.comp_apply]
    exact hm'.symm

theorem AugBij_of_loc (hS : Sep) (hG : Glue) (hSu : LocSurj) (hI : LocInj) : LateralTheory.E.TateTwistZeroAugmentationBijective.AugBij := by
  intro q φ hnat hgen
  have inj : ∀ T : Scheme.{0}, IsUnit (q : Γ(T, ⊤)) → Function.Injective (φ T) := by
    intro T hT
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨ι, V, g, he, hs, h0⟩ := hI q φ hnat hgen T hT x hx
    exact hS _ _ T ι V g he hs x 0 (fun i => by rw [h0 i]; exact (map_zero ((tw q 0).obj.map (g i).op).hom).symm)
  intro T hT
  refine ⟨inj T hT, fun f => ?_⟩
  obtain ⟨ι, V, g, he, hs, hy⟩ := hSu q φ hnat hgen T hT f
  choose y hy using hy
  obtain ⟨z, hz⟩ := hG _ _ T ι V g he hs y (fun i j => by
    apply inj _ (unit_res (pullback.fst (g i) (g j) ≫ g i) hT)
    rw [hnat, hnat, hy i, hy j]
    ext t
    simp only [LocallyConstant.coe_comap, Function.comp_apply]
    erw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    rfl)
  refine ⟨z, ?_⟩
  ext t
  obtain ⟨i, v, rfl⟩ := hs t
  have := congrArg (fun k : LocallyConstant (V i) (ZMod q) => k v) ((hnat (g i) z).symm.trans ((congrArg (φ (V i)) (hz i)).trans (hy i)))
  simpa using this

def SecLoc : Prop := ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (T : Scheme.{0})
  (x : Sec (ofRings R M) T), ∃ (ι : Type) (V : ι → Scheme.{0}) (g : ∀ i, V i ⟶ T), (∀ i, Etale (g i)) ∧
    (∀ t : T, ∃ i, ∃ v : V i, (g i).base v = t) ∧ ∀ i, ∃ a : M.obj Γ(V i, ⊤), Sec.res (g i) x = ofRings.sec M (V i) a

def GenEq : Prop := ∀ (q : ℕ) (U : Scheme.{0}) (ξ ζ : Prim q Γ(U, ⊤)), twGen 0 ξ = twGen 0 ζ

theorem secEq (hE : GenEq) {q : ℕ} {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (a : (twF q 0).obj Γ(U, ⊤)) :
    ∃ m : ℤ, ofRings.sec (twF q 0) U a = m • twGen 0 ζ := by
  induction a using Submodule.Quotient.induction_on with
  | H a =>
  induction a using Finsupp.induction_linear with
  | zero => exact ⟨0, by rw [zero_smul]; exact map_zero ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).app _).hom⟩
  | add a b ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    rw [add_smul, ← hm, ← hn, Submodule.Quotient.mk_add]
    exact map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).app _).hom _ _
  | single ξ c =>
    refine ⟨(c.down.cast : ℤ), ?_⟩
    have h1 : Finsupp.single ξ c = c • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h1, Submodule.Quotient.mk_smul]
    have h2 : ofRings.sec (twF q 0) U (c • Submodule.Quotient.mk (Finsupp.single ξ 1)) =
        c • twGen 0 ξ := map_smul ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).app _).hom _ _
    refine h2.trans ?_
    rw [hE q U ξ ζ, ← Int.cast_smul_eq_zsmul (ULift.{1} (ZMod q))]
    congr 1
    apply ULift.ext
    rw [ULift.down_intCast, ZMod.intCast_cast, ZMod.cast_id', id_eq]

theorem LocInj_of (hR : Root) (hL : SecLoc) (hE : GenEq) : LocInj := by
  intro q φ hnat hgen T hT x hx
  obtain ⟨W, h, he, hs, ⟨ζ⟩⟩ := hR q T hT
  obtain ⟨ι, V, g, hge, hgs, ha⟩ := hL (ZMod q) (twF q 0) W (Sec.res h x)
  choose a ha using ha
  refine ⟨{i // Nonempty (V i)}, fun i => V i.1, fun i => g i.1 ≫ h, fun i => by haveI := hge i.1; haveI := he; infer_instance,
    ?_, ?_⟩
  · intro t
    obtain ⟨w, rfl⟩ := hs t
    obtain ⟨i, v, rfl⟩ := hgs w
    exact ⟨⟨i, ⟨v⟩⟩, v, by rw [Scheme.Hom.comp_apply]⟩
  · rintro ⟨i, ⟨v⟩⟩
    obtain ⟨m, hm⟩ := secEq hE (ζ.map (g i).appTop.hom) (a i)
    have hx' : Sec.res (g i ≫ h) x = m • twGen 0 (ζ.map (g i).appTop.hom) :=
      (res_comp (g i) h x).symm.trans ((ha i).trans hm)
    have h0 : φ (V i) (Sec.res (g i ≫ h) x) = 0 := by rw [hnat, hx]; rfl
    rw [hx', map_zsmul, hgen] at h0
    have h3 : (m : ZMod q) = 0 := by
      have := congrArg (fun k : LocallyConstant (V i) (ZMod q) => k v) h0
      change m • (1 : ZMod q) = 0 at this
      rwa [zsmul_eq_mul, mul_one] at this
    show Sec.res (g i ≫ h) x = 0
    rw [hx', ← Int.cast_smul_eq_zsmul (ULift.{1} (ZMod q))]
    have h4 : ((m : ULift.{1} (ZMod q))) = 0 := by apply ULift.ext; simpa using h3
    rw [h4, zero_smul]

theorem secLoc' : SecLoc := by
  intro R _ M T x
  have hmem := Presheaf.imageSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ M)) (U := Opposite.op T) x
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hmem
  have hc := (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).1 𝒰.mem₀
  refine ⟨𝒰.I₀, 𝒰.X, 𝒰.f, hc.2, fun t => ?_, fun i => ?_⟩
  · obtain ⟨i, v, hv⟩ := hc.1 t; exact ⟨i, v, hv⟩
  · obtain ⟨a, ha⟩ := @h𝒰 _ (𝒰.f i) (by exact Presieve.ofArrows.mk i)
    exact ⟨a, ha.symm⟩

theorem twGen_res {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen 0 ζ) = twGen 0 (ζ.map g.appTop.hom) := by
  have h := congrArg (fun k => (ModuleCat.Hom.hom k) (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))))
    ((toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ twF q 0)).naturality g.op)
  refine h.symm.trans ?_
  change ((toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ twF q 0)).app (Opposite.op V)).hom
    (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ 1))) = _
  rw [Finsupp.mapDomain_single]
  rfl

theorem twGen_eq_of_pow {q : ℕ} {U : Scheme.{0}} (ξ ζ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGen 0 ξ = twGen 0 ζ := by
  unfold twGen
  congr 1
  apply (Submodule.Quotient.eq _).2
  apply Submodule.subset_span
  refine ⟨ζ, ξ, a, h, ?_⟩
  simp
  rfl

def ZarPow : Prop := ∀ (q : ℕ) (U : Scheme.{0}) (ξ ζ : Prim q Γ(U, ⊤)) (u : U),
  ∃ (O : U.Opens) (a : (ZMod q)ˣ), u ∈ O ∧ (ξ.map O.ι.appTop.hom).1 = (ζ.map O.ι.appTop.hom).1 ^ (a : ZMod q).val

theorem GenEq_of (hZ : ZarPow) : GenEq := by
  intro q U ξ ζ
  choose O a hu ha using hZ q U ξ ζ
  refine Sep_holds (ZMod q) (tw q 0) U U (fun u => (O u : Scheme.{0})) (fun u => (O u).ι) (fun u => inferInstance) ?_ _ _ ?_
  · intro t
    have ht : t ∈ Set.range (O t).ι.base := by rw [Scheme.Opens.range_ι]; exact hu t
    obtain ⟨v, hv⟩ := ht
    exact ⟨t, v, hv⟩
  · intro u
    rw [twGen_res, twGen_res]
    exact twGen_eq_of_pow _ _ (a u) (ha u)

def LocPow : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (ξ ζ : Prim q A),
  ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val

theorem ZarPow_of (hL : LocPow) : ZarPow := by
  intro q U ξ ζ u
  obtain ⟨a, ha⟩ := hL q (U.presheaf.stalk u) (ξ.map (U.presheaf.germ ⊤ u trivial).hom) (ζ.map (U.presheaf.germ ⊤ u trivial).hom)
  have h : U.presheaf.germ ⊤ u trivial ξ.1 = U.presheaf.germ ⊤ u trivial (ζ.1 ^ (a : ZMod q).val) := by
    rw [map_pow]; exact ha
  obtain ⟨W, hW, i1, i2, he⟩ := U.presheaf.germ_eq (U := ⊤) (V := ⊤) u trivial trivial _ _ h
  refine ⟨W, a, hW, ?_⟩
  show (Scheme.Opens.ι (X := U) W).appTop.hom ξ.1 = ((Scheme.Opens.ι (X := U) W).appTop.hom ζ.1) ^ _
  rw [← map_pow, Scheme.Opens.ι_appTop]
  have hle : (Scheme.Opens.ι (X := U) W) ''ᵁ ⊤ ≤ W := by simp
  have := congrArg (U.presheaf.map (homOfLE hle).op).hom he
  simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp] at this
  exact (congrArg (fun k => (U.presheaf.map (Quiver.Hom.op k)).hom ξ.1) (Subsingleton.elim _ _)).trans
    (this.trans (congrArg (fun k => (U.presheaf.map (Quiver.Hom.op k)).hom (ζ.1 ^ (a : ZMod q).val)) (Subsingleton.elim _ _)))

end LateralTheory.E.AugBijPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CovOfPoints
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSurj0Pf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem cov_of_points {B : Scheme.{0}} (U : B.Etale) (P : ∀ U' : B.Etale, (U' ⟶ U) → Prop)
    (h : ∀ x : U.left, ∃ (U' : B.Etale) (a : U' ⟶ U), x ∈ Set.range a.left ∧
      ∀ (U'' : B.Etale) (b : U'' ⟶ U'), P U'' (b ≫ a)) : Cov U P := by
  choose Z f hx hP using h
  refine ⟨Sieve.ofArrows Z f, ?_, ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, hx x⟩
  · rintro U' a ⟨Y, b, g, ⟨j⟩, rfl⟩
    exact hP j U' b

def LeafSurj0W : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g2 ≫ g1 ≫ p) ι U)) (tw q i) 0,
  ∀ x : U.left, U.hom x ∈ Set.range ι → ∃ (U' : B.Etale) (a : U' ⟶ U), x ∈ Set.range a.left ∧
    ∀ (U'' : B.Etale) (b : U'' ⟶ U'), rY q i (g2 ≫ g1 ≫ p) ι (b ≫ a) 0 y = 0

def LeafSurj0V : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g2 ≫ g1 ≫ p) ι U)) (tw q i) 0,
  ∀ x : U.left, U.hom x ∈ V → ∃ (U' : B.Etale) (a : U' ⟶ U), x ∈ Set.range a.left ∧
    ∀ (U'' : B.Etale) (b : U'' ⟶ U'), ∃ c : Hrel (ZMod q) (sch.map (prB ι U'')) (tw q i) 0,
      bY q i (g2 ≫ g1 ≫ p) ι U'' 0 c = rY q i (g2 ≫ g1 ≫ p) ι (b ≫ a) 0 y

theorem LeafSurj0_of (hW : LeafSurj0W) (hV : LeafSurj0V) : LateralTheory.E.LeafDegCut.LeafSurj0 := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hVW p g1 g2 h0 h1 h2 hS U y
  refine cov_of_points U _ fun x => ?_
  by_cases hx : U.hom x ∈ V
  · exact hV hy q k hq i b ι V hVW p g1 g2 h0 h1 h2 hS U y x hx
  · have hxW : U.hom x ∈ Set.range ι := by
      have : U.hom x ∉ (V : Set B) := hx
      rw [hVW] at this
      simpa using this
    obtain ⟨U', a, hxa, hz⟩ := hW hy q k hq i b ι V hVW p g1 g2 h0 h1 h2 hS U y x hxW
    exact ⟨U', a, hxa, fun U'' b' => ⟨0, by rw [map_zero, hz U'' b']⟩⟩

end LateralTheory.E.LeafSurj0Pf
end
end

