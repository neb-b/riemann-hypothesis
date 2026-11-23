module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0180
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesOfExact
section
noncomputable section

namespace GlobalTheory.AdmLoc

section Ss

variable {R : Type} [Ring R]
variable {M M' A A' C C' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
  [AddCommGroup C] [Module R C] [AddCommGroup C'] [Module R C']

theorem subquot_map {f : A →ₗ[R] M} (hf : Function.Injective f) (X Y : Submodule R A) {X' Y' : Submodule R M}
    (hX : X' = X.map f) (hY : Y' = Y.map f) :
    Nonempty ((↥Y ⧸ X.comap Y.subtype) ≃ₗ[R] (↥Y' ⧸ X'.comap Y'.subtype)) := by
  subst hX hY
  refine ⟨Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf Y) ?_⟩
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, congrArg Subtype.val hxy⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hxx⟩ := hy
    obtain rfl : x' = x := hf hxx
    exact ⟨⟨x', hx'⟩, hx, rfl⟩

theorem subquot_comap {g : M →ₗ[R] C} (hg : Function.Surjective g) (X Y : Submodule R C) {X' Y' : Submodule R M}
    (hX : X' = X.comap g) (hY : Y' = Y.comap g) :
    Nonempty ((↥Y ⧸ X.comap Y.subtype) ≃ₗ[R] (↥Y' ⧸ X'.comap Y'.subtype)) := by
  subst hX hY
  let p : ↥(Y.comap g) →ₗ[R] ↥Y := g.restrict (fun _ h => h)
  let q : ↥(Y.comap g) →ₗ[R] (↥Y ⧸ X.comap Y.subtype) := (Submodule.mkQ _).comp p
  have hp : Function.Surjective p := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hq : Function.Surjective q := (Submodule.mkQ_surjective _).comp hp
  have hk : (X.comap g).comap (Y.comap g).subtype = LinearMap.ker q := by
    ext x
    exact (Submodule.Quotient.mk_eq_zero (X.comap Y.subtype) (x := p x)).symm
  exact ⟨((Submodule.quotEquivOfEq _ _ hk).trans (q.quotKerEquivOfSurjective hq)).symm⟩

theorem exists_series_of_exact {f : A →ₗ[R] M} {g : M →ₗ[R] C} (hf : Function.Injective f)
    (hg : Function.Surjective g) (H : Function.Exact f g)
    (t : CompositionSeries (Submodule R A)) (ht₁ : t.head = ⊥) (ht₂ : t.last = ⊤)
    (s : CompositionSeries (Submodule R C)) (hs₁ : s.head = ⊥) (hs₂ : s.last = ⊤) :
    ∃ r : CompositionSeries (Submodule R M), r.head = ⊥ ∧ r.last = ⊤ ∧
      ∃ e : Fin t.length ⊕ Fin s.length ≃ Fin r.length,
        (∀ i, Nonempty (factor t i ≃ₗ[R] factor r (e (Sum.inl i)))) ∧
        ∀ j, Nonempty (factor s j ≃ₗ[R] factor r (e (Sum.inr j))) := by
  let s' : CompositionSeries (Submodule R M) :=
    { length := s.length
      toFun := fun i => (s i).comap g
      step := fun i => Submodule.comap_covBy_of_surjective hg (s.step i) }
  let t' : CompositionSeries (Submodule R M) :=
    { length := t.length
      toFun := fun i => (t i).map f
      step := fun i => Submodule.map_covBy_of_injective hf (t.step i) }
  have hc : t'.last = s'.head := by
    change t.last.map f = s.head.comap g
    rw [ht₂, hs₁, Submodule.map_top, Submodule.comap_bot, LinearMap.exact_iff.mp H]
  refine ⟨t'.smash s' hc, ?_, ?_, finSumFinEquiv, fun i => ?_, fun j => ?_⟩
  · rw [RelSeries.head_smash]
    change t.head.map f = ⊥
    rw [ht₁, Submodule.map_bot]
  · rw [RelSeries.last_smash]
    change s.last.comap g = ⊤
    rw [hs₂, Submodule.comap_top]
  · exact subquot_map hf _ _ (RelSeries.smash_castAdd hc i) (RelSeries.smash_succ_castAdd hc i)
  · exact subquot_comap hg _ _ (RelSeries.smash_natAdd hc j) (RelSeries.smash_succ_natAdd hc j)

theorem SameFactors.finiteLength_left (h : SameFactors R M M') : IsFiniteLength R M := by
  obtain ⟨s, -, h1, h2, -⟩ := h
  exact isFiniteLength_of_exists_compositionSeries ⟨s, h1, h2⟩

theorem SameFactors.finiteLength_right (h : SameFactors R M M') : IsFiniteLength R M' :=
  h.symm.finiteLength_left

theorem SameFactors.of_exact_of_exact {f : A →ₗ[R] M} {g : M →ₗ[R] C} (hf : Function.Injective f)
    (hg : Function.Surjective g) (H : Function.Exact f g)
    {f' : A' →ₗ[R] M'} {g' : M' →ₗ[R] C'} (hf' : Function.Injective f')
    (hg' : Function.Surjective g') (H' : Function.Exact f' g')
    (hA : SameFactors R A A') (hC : SameFactors R C C') : SameFactors R M M' := by
  obtain ⟨t, t', ht1, ht2, ht3, ht4, a, ha⟩ := hA
  obtain ⟨s, s', hs1, hs2, hs3, hs4, c, hc⟩ := hC
  obtain ⟨r, hr1, hr2, e, he1, he2⟩ := exists_series_of_exact hf hg H t ht1 ht2 s hs1 hs2
  obtain ⟨r', hr3, hr4, e', he3, he4⟩ := exists_series_of_exact hf' hg' H' t' ht3 ht4 s' hs3 hs4
  refine ⟨r, r', hr1, hr2, hr3, hr4, e.symm.trans ((a.sumCongr c).trans e'), fun k => ?_⟩
  obtain ⟨k, rfl⟩ := e.surjective k
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]
  rcases k with i | j
  · obtain ⟨u⟩ := he1 i
    obtain ⟨v⟩ := ha i
    obtain ⟨w⟩ := he3 (a i)
    exact ⟨(u.symm.trans v).trans w⟩
  · obtain ⟨u⟩ := he2 j
    obtain ⟨v⟩ := hc j
    obtain ⟨w⟩ := he4 (c j)
    exact ⟨(u.symm.trans v).trans w⟩

theorem SameFactors.of_exact {f : A →ₗ[R] M} {g : M →ₗ[R] C} (hf : Function.Injective f)
    (hg : Function.Surjective g) (H : Function.Exact f g) (h : IsFiniteLength R M) :
    SameFactors R M (A × C) :=
  SameFactors.of_exact_of_exact hf hg H LinearMap.inl_injective LinearMap.snd_surjective .inl_snd
    (SameFactors.refl (h.of_injective hf)) (SameFactors.refl (h.of_surjective hg))

theorem SameFactors.sub_prod_quot (h : IsFiniteLength R M) (S : Submodule R M) :
    SameFactors R M (↥S × (M ⧸ S)) :=
  SameFactors.of_exact S.subtype_injective S.mkQ_surjective (LinearMap.exact_subtype_mkQ S) h

theorem SameFactors.prod (hA : SameFactors R A A') (hC : SameFactors R C C') :
    SameFactors R (A × C) (A' × C') :=
  SameFactors.of_exact_of_exact LinearMap.inl_injective LinearMap.snd_surjective .inl_snd
    LinearMap.inl_injective LinearMap.snd_surjective .inl_snd hA hC

theorem SameFactors.congr (h : SameFactors R A A') (e : A ≃ₗ[R] C) (e' : A' ≃ₗ[R] C') : SameFactors R C C' :=
  ((SameFactors.of_equiv h.finiteLength_left e).symm.trans h).trans (SameFactors.of_equiv h.finiteLength_right e')

theorem SameFactors.of_subsingleton [Subsingleton A] [Subsingleton A'] : SameFactors R A A' :=
  SameFactors.of_equiv IsFiniteLength.of_subsingleton (LinearEquiv.ofSubsingleton _ _)

theorem SameFactors.pi_fin : ∀ {m : ℕ} {N N' : Fin m → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
    [∀ j, AddCommGroup (N' j)] [∀ j, Module R (N' j)], (∀ j, SameFactors R (N j) (N' j)) →
    SameFactors R (∀ j, N j) (∀ j, N' j)
  | 0, _, _, _, _, _, _, _ => SameFactors.of_subsingleton
  | _ + 1, N, N', _, _, _, _, h =>
    ((h 0).prod (SameFactors.pi_fin fun j => h (Fin.succ j))).congr
      (Fin.consLinearEquiv R N) (Fin.consLinearEquiv R N')

theorem SameFactors.pi {ι : Type} [Finite ι] {N N' : ι → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
    [∀ j, AddCommGroup (N' j)] [∀ j, Module R (N' j)] (h : ∀ j, SameFactors R (N j) (N' j)) :
    SameFactors R (∀ j, N j) (∀ j, N' j) := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  exact (SameFactors.pi_fin (N := fun j => N (e.symm j)) (N' := fun j => N' (e.symm j))
    fun j => h (e.symm j)).congr (LinearEquiv.piCongrLeft R N e.symm) (LinearEquiv.piCongrLeft R N' e.symm)

end Ss

section Rep

variable {O G : Type} [CommRing O] [Group G]
variable {M M' A A' C C' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
  [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O A']
  [AddCommGroup C] [Module O C] [AddCommGroup C'] [Module O C']

def asModuleMap {π : Representation O G M} {π' : Representation O G M'} (f : M →ₗ[O] M')
    (hf : ∀ g x, f (π g x) = π' g (f x)) : π.asModule →ₗ[MonoidAlgebra O G] π'.asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule π π'
    { toLinearMap := f, isIntertwining' := fun g => LinearMap.ext (hf g) }

def equivAsModule {π : Representation O G M} {π' : Representation O G M'} (e : M ≃ₗ[O] M')
    (he : ∀ g x, e (π g x) = π' g (e x)) : π.asModule ≃ₗ[MonoidAlgebra O G] π'.asModule :=
  LinearEquiv.ofBijective (asModuleMap e.toLinearMap he) e.bijective

def piAsModule {ι : Type} {N : ι → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module O (N j)]
    (π : ∀ j, Representation O G (N j)) :
    (piRep π).asModule ≃ₗ[MonoidAlgebra O G] ∀ j, (π j).asModule :=
  LinearEquiv.ofBijective
    (LinearMap.pi fun j => asModuleMap (π := piRep π) (π' := π j) (LinearMap.proj j) fun _ _ => rfl)
    (Function.bijective_id (α := ∀ j, N j))

theorem finiteLength_asModule (π : Representation O G M) (h : IsFiniteLength O M) :
    IsFiniteLength (MonoidAlgebra O G) π.asModule := by
  have h' : IsFiniteLength O π.asModule := h.of_injective (f := π.asModuleEquiv.toLinearMap) π.asModuleEquiv.injective
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at h' ⊢
  exact ⟨isNoetherian_of_tower O h'.1, isArtinian_of_tower O h'.2⟩

variable {π : Representation O G M} {π' : Representation O G M'} {α : Representation O G A}
  {α' : Representation O G A'} {γ : Representation O G C} {γ' : Representation O G C'}

theorem SameSS.refl' (h : IsFiniteLength (MonoidAlgebra O G) π.asModule) : SameSS π π := SameFactors.refl h

theorem SameSS.refl (π : Representation O G M) (h : IsFiniteLength O M) : SameSS π π :=
  SameFactors.refl (finiteLength_asModule π h)

theorem SameSS.symm (h : SameSS π π') : SameSS π' π := SameFactors.symm h

theorem SameSS.trans (h : SameSS π π') (h' : SameSS π' α) : SameSS π α := SameFactors.trans h h'

theorem SameSS.of_equiv (h : IsFiniteLength O M) (e : M ≃ₗ[O] M') (he : ∀ g x, e (π g x) = π' g (e x)) :
    SameSS π π' :=
  SameFactors.of_equiv (finiteLength_asModule π h) (equivAsModule e he)

theorem SameSS.congr (h : SameSS α α') (e : A ≃ₗ[O] C) (he : ∀ g x, e (α g x) = γ g (e x))
    (e' : A' ≃ₗ[O] C') (he' : ∀ g x, e' (α' g x) = γ' g (e' x)) : SameSS γ γ' :=
  SameFactors.congr h (equivAsModule e he) (equivAsModule e' he')

theorem SameSS.congr_left (h : SameSS α π) (e : A ≃ₗ[O] C) (he : ∀ g x, e (α g x) = γ g (e x)) : SameSS γ π :=
  h.congr e he (LinearEquiv.refl O M) fun _ _ => rfl

theorem SameSS.congr_right (h : SameSS π α) (e : A ≃ₗ[O] C) (he : ∀ g x, e (α g x) = γ g (e x)) : SameSS π γ :=
  h.congr (LinearEquiv.refl O M) (fun _ _ => rfl) e he

theorem SameSS.of_exact_of_exact {f : A →ₗ[O] M} {p : M →ₗ[O] C}
    (ef : ∀ g x, f (α g x) = π g (f x)) (ep : ∀ g x, p (π g x) = γ g (p x))
    (hf : Function.Injective f) (hp : Function.Surjective p) (H : Function.Exact f p)
    {f' : A' →ₗ[O] M'} {p' : M' →ₗ[O] C'}
    (ef' : ∀ g x, f' (α' g x) = π' g (f' x)) (ep' : ∀ g x, p' (π' g x) = γ' g (p' x))
    (hf' : Function.Injective f') (hp' : Function.Surjective p') (H' : Function.Exact f' p')
    (hA : SameSS α α') (hC : SameSS γ γ') : SameSS π π' :=
  SameFactors.of_exact_of_exact (R := MonoidAlgebra O G) (M := π.asModule) (M' := π'.asModule)
    (A := α.asModule) (A' := α'.asModule) (C := γ.asModule) (C' := γ'.asModule)
    (f := asModuleMap f ef) (g := asModuleMap p ep) hf hp H
    (f' := asModuleMap f' ef') (g' := asModuleMap p' ep') hf' hp' H' hA hC

theorem SameSS.of_exact' {f : A →ₗ[O] M} {p : M →ₗ[O] C}
    (ef : ∀ g x, f (α g x) = π g (f x)) (ep : ∀ g x, p (π g x) = γ g (p x))
    (hf : Function.Injective f) (hp : Function.Surjective p) (H : Function.Exact f p)
    (h : IsFiniteLength (MonoidAlgebra O G) π.asModule) : SameSS π (α.prod γ) :=
  SameSS.of_exact_of_exact ef ep hf hp H (f' := LinearMap.inl O A C) (p' := LinearMap.snd O A C)
    (α' := α) (γ' := γ) (fun g x => by simp) (fun g x => by simp)
    LinearMap.inl_injective LinearMap.snd_surjective .inl_snd
    (SameSS.refl' (IsFiniteLength.of_injective (M := α.asModule) (N := π.asModule) (f := asModuleMap f ef) h hf))
    (SameSS.refl' (IsFiniteLength.of_surjective (M := π.asModule) (N := γ.asModule) (f := asModuleMap p ep) h hp))

theorem SameSS.of_exact {f : A →ₗ[O] M} {p : M →ₗ[O] C}
    (ef : ∀ g x, f (α g x) = π g (f x)) (ep : ∀ g x, p (π g x) = γ g (p x))
    (hf : Function.Injective f) (hp : Function.Surjective p) (H : Function.Exact f p)
    (h : IsFiniteLength O M) : SameSS π (α.prod γ) :=
  SameSS.of_exact' ef ep hf hp H (finiteLength_asModule π h)

theorem SameSS.prod (hA : SameSS α α') (hC : SameSS γ γ') : SameSS (α.prod γ) (α'.prod γ') :=
  SameSS.of_exact_of_exact (f := LinearMap.inl O A C) (p := LinearMap.snd O A C)
    (fun g x => by simp) (fun g x => by simp) LinearMap.inl_injective LinearMap.snd_surjective .inl_snd
    (f' := LinearMap.inl O A' C') (p' := LinearMap.snd O A' C')
    (fun g x => by simp) (fun g x => by simp) LinearMap.inl_injective LinearMap.snd_surjective .inl_snd hA hC

theorem SameSS.piRep {ι : Type} [Finite ι] {N N' : ι → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module O (N j)]
    [∀ j, AddCommGroup (N' j)] [∀ j, Module O (N' j)] {σ : ∀ j, Representation O G (N j)}
    {σ' : ∀ j, Representation O G (N' j)} (h : ∀ j, SameSS (σ j) (σ' j)) : SameSS (piRep σ) (piRep σ') :=
  (SameFactors.pi (N := fun j => (σ j).asModule) (N' := fun j => (σ' j).asModule) h).congr
    (piAsModule σ).symm (piAsModule σ').symm

end Rep

end GlobalTheory.AdmLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicProjectorMemBreuilKisinLattice
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CokerL

theorem isoProj_mem_L : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), v ∈ P.L → GlobalTheory.CokerL.isoProj Δ c v ∈ P.L := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ P Δ c v hv
  letI := Fintype.ofFinite (rootsOfUnity e K)
  have key : ∀ s : ZMod a → K, (∀ τ, ‖s τ‖ ≤ 1) → ∀ w ∈ P.L, diagScale K a ι s w ∈ P.L := by
    intro s hs w hw
    have h : diagScale K a ι s w = (fun τ => C (s τ)) • w := by
      ext τ i
      simp [diagScale_apply, Pi.smul_apply', PowerSeries.smul_eq_C_mul]
    rw [h]
    refine P.smul_tot_mem_ext (fun τ => mem_A.2 fun n => ?_) hw
    rw [coeff_C]
    split_ifs
    · exact hs τ
    · simp
  have hnd : ¬ l ∣ e := by
    intro h
    have h1 : l ∣ e + 1 := by
      rw [TameDescentExponentData.succ_eq (K := K) (l := l) (e := e) (a := a)]
      exact dvd_pow_self l (NeZero.ne a)
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h1))
  have he : ‖(e : K)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_natCast_eq l, Padic.norm_natCast_eq_one_iff.2
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hnd), inv_one]
  have hsc : isoProj Δ c v = diagScale K a ι (fun _ => (e : K)⁻¹) (∑ ζ : rootsOfUnity e K,
      diagScale K a ι (fun τ => ((TameGal.inertia ζ : TameGal K l e a).root τ)⁻¹ ^ c.val)
        (Δ.act (TameGal.inertia ζ) v)) := by
    simp only [isoProj, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    rfl
  rw [hsc]
  refine key _ (fun _ => he) _ (Submodule.sum_mem _ fun ζ _ => key _ (fun τ => ?_) _ ?_)
  · rw [norm_pow, norm_inv, TameGal.norm_root, inv_one, one_pow]
  · exact Δ.act_mem_ext _ le_rfl rot_A hv

end GlobalTheory.CokerL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicProjectorMemIsotypicPartExplicit
section
noncomputable section

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]


omit [NeZero e] in
theorem act_inertia_diagScale {P : PhiMod O K l e a ι} (Δ : Descent P) (ξ : rootsOfUnity e K)
    (s : ZMod a → K) (w : Vec K a ι) :
    Δ.act (TameGal.inertia ξ) (diagScale K a ι s w) =
      diagScale K a ι s (Δ.act (TameGal.inertia ξ) w) := by
  have h1 (u : Vec K a ι) : diagScale K a ι s u = (fun τ => (C (s τ) : K⟦X⟧)) • u := by
    ext τ i : 2
    simp [diagScale_apply, smul_eq_C_mul]
  have h2 : ringAct (TameGal.inertia ξ : TameGal K l e a) (fun τ => (C (s τ) : K⟦X⟧)) =
      fun τ => C (s τ) := by
    ext τ n
    rw [ringAct_apply, TameGal.shift_inertia, sub_zero, coeff_rescale, coeff_C]
    split_ifs with h <;> simp [h]
  rw [h1, h1, Δ.act_smul_tot, h2]

theorem isoProj_mem_isotypic {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e)
    (v : Vec K a ι) : isoProj Δ c v ∈ Δ.isotypic c := by
  letI := Fintype.ofFinite (rootsOfUnity e K)
  unfold isoProj
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  intro ξ τ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, act_inertia_diagScale,
    Finset.sum_apply, diagScale_apply, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft ξ) _ _ fun ζ => ?_
  rw [Equiv.coe_mulLeft, ← Module.End.mul_apply, ← map_mul, ← map_mul, smul_smul]
  congr 1
  rw [map_mul, TameGal.root_mul, TameGal.shift_inertia, sub_zero, ← mul_pow, mul_inv,
    mul_inv_cancel_left₀ (TameGal.root_ne_zero _ _)]

theorem isoProj_mem_isotypic' : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι)
    (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), GlobalTheory.CokerL.isoProj Δ c v ∈ Δ.isotypic c :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Δ c v => isoProj_mem_isotypic Δ c v

end GlobalTheory.CokerL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticePowSmulNhdsZeroBasis
section
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

namespace GlobalTheory


open Filter Topology in
open scoped TensorProduct in
theorem _root_.GlobalTheory.lattice_multiples_nhds_basis :
    ∀ (LL O V : Type) [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [IsModuleTopology LL V] (T : Submodule O V) (lam : O), T.FG → Submodule.span LL (T : Set V) = ⊤ → IsOpen (Set.range (algebraMap O LL)) → algebraMap O LL lam ≠ 0 → (∀ U ∈ 𝓝 (0 : LL), ∃ a : ℕ, ∀ x : O, algebraMap O LL (lam ^ a * x) ∈ U) → (∀ a : ℕ, {v : V | ∃ t ∈ T, v = lam ^ a • t} ∈ 𝓝 (0 : V)) ∧ ∀ U ∈ 𝓝 (0 : V), ∃ a : ℕ, ∀ t ∈ T, lam ^ a • t ∈ U := by
  intro LL O V _ _ _ _ _ _ _ _ _ _ _ T lam hT hspan hopen hlam hsmall
  obtain ⟨n, s, rfl⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hT
  set φ : (Fin n → LL) →ₗ[LL] V := Fintype.linearCombination LL s with hφ
  have key : ∀ (a : ℕ) (c : Fin n → O),
      φ (fun i => algebraMap O LL (lam ^ a * c i)) = lam ^ a • ∑ i, c i • s i := by
    intro a c
    simp only [hφ, Fintype.linearCombination_apply, Finset.smul_sum, map_mul, mul_smul,
      algebraMap_smul]
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    intro t ht
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp ht
    exact ⟨_, by rw [key 0 c, pow_zero, one_smul]⟩
  have hq := IsModuleTopology.isOpenQuotientMap_of_surjective hsurj
  refine ⟨fun a => ?_, fun U hU => ?_⟩
  · have hc : algebraMap O LL (lam ^ a) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hlam
    set W : Set LL := Set.range fun x : O => algebraMap O LL (lam ^ a * x) with hW
    have hWeq : W = (Homeomorph.mulLeft₀ _ hc) '' Set.range (algebraMap O LL) := by
      ext y; simp [hW, map_mul]
    have hWo : IsOpen W := hWeq ▸ (Homeomorph.mulLeft₀ _ hc).isOpenMap _ hopen
    have hPo : IsOpen (φ '' Set.univ.pi fun _ => W) :=
      hq.isOpenMap _ (isOpen_set_pi Set.finite_univ fun _ _ => hWo)
    refine mem_of_superset (hPo.mem_nhds ⟨0, fun i _ => ⟨0, by simp⟩, map_zero φ⟩) ?_
    rintro v ⟨y, hy, rfl⟩
    choose c hc' using fun i => hy i (Set.mem_univ i)
    have : y = fun i => algebraMap O LL (lam ^ a * c i) := funext fun i => (hc' i).symm
    subst this
    exact ⟨_, (Submodule.mem_span_range_iff_exists_fun O).mpr ⟨c, rfl⟩, key a c⟩
  · have h0 : φ ⁻¹' U ∈ 𝓝 (0 : Fin n → LL) :=
      hq.continuous.continuousAt.preimage_mem_nhds (by simpa using hU)
    rw [nhds_pi, Filter.mem_pi'] at h0
    obtain ⟨I, t, ht, hsub⟩ := h0
    obtain ⟨a, ha⟩ := hsmall (⋂ i, t i) (Filter.iInter_mem.mpr ht)
    refine ⟨a, fun v hv => ?_⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp hv
    rw [← key a c]
    exact hsub fun i _ => Set.mem_iInter.mp (ha (c i)) i

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LogDefectCoeffEqZero
section
open GlobalTheory.LogU

namespace GlobalTheory.LogU

open MvPolynomial

theorem logDefect_coeff_eq_zero : ∀ (n i j : ℕ), i + j < n →
    AddMonoidAlgebra.coeff (GlobalTheory.LogU.logDefect n) (Finsupp.single 0 i + Finsupp.single 1 j) = 0 := by
  intro n i j hij
  let J : Ideal (MvPolynomial (Fin 2) ℚ) := MvPolynomial.idealOfVars (Fin 2) ℚ
  let q : MvPolynomial (Fin 2) ℚ →+* MvPolynomial (Fin 2) ℚ ⧸ J ^ n := Ideal.Quotient.mk _
  have hR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : MvPolynomial (Fin 2) ℚ ⧸ J ^ n) := fun m hm => by
    have hu : IsUnit ((m : ℚ)) := (Nat.cast_ne_zero.2 hm).isUnit
    simpa using hu.map (q.comp MvPolynomial.C)
  have hI : (J.map q) ^ n = ⊥ := by
    rw [← Ideal.map_pow]; exact Ideal.map_quotient_self _
  have hXJ : ∀ k, (X k : MvPolynomial (Fin 2) ℚ) ∈ J := fun k =>
    Ideal.subset_span (Set.mem_range_self k)
  have key := GlobalTheory.MemLoc.LogAdd.trunc_add hR n _ hI (q (X 0)) (q (X 1))
    (Ideal.mem_map_of_mem q (hXJ 0)) (Ideal.mem_map_of_mem q (hXJ 1))
  have h0 : MvPolynomial.aeval ![q (X 0), q (X 1)] (logDefect n) = 0 := by
    refine (aeval_logDefect n (q (X 0)) (q (X 1))).trans ?_
    simp only [truncLogF]; rw [key]; ring
  have hcomp : q.comp (MvPolynomial.map (Int.castRingHom ℚ)) =
      (MvPolynomial.aeval (R := ℤ) ![q (X 0), q (X 1)]).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro k; fin_cases k <;> simp
  have hφ : q (MvPolynomial.map (Int.castRingHom ℚ) (logDefect n)) = 0 := by
    have := RingHom.congr_fun hcomp (logDefect n)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [this, h0]
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_pow_idealOfVars_iff'] at hφ
  have hd : (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j).degree < n := by
    first
      | simpa [Finsupp.degree_single] using hij
      | simpa [Finsupp.degree, Finsupp.support_single_ne_zero] using hij
  have := hφ _ hd
  rw [MvPolynomial.coeff_map] at this
  simpa using this

end GlobalTheory.LogU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPrimePowLatticeOfXPowSmulMem
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CokerL

open Matrix

theorem inv_mul_coeff_eq_of_X_pow_mul {K : Type} [Field K] {N : ℕ} {c : K} (hc : c ≠ 0)
    {f g : K⟦X⟧} (h : X ^ N * f = c • g) (k : ℕ) : c⁻¹ * coeff k f = coeff (k + N) g := by
  have := congrArg (coeff (k + N)) h
  rw [coeff_X_pow_mul, coeff_smul, smul_eq_mul] at this
  rw [this, inv_mul_cancel_left₀ hc]

theorem mem_lpow_L_of_vpow_smul (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] (P : PhiMod O K l e a ι) (n b : ℕ) (w z : Vec K a ι) (hw : w ∈ P.L)
    (hz : z ∈ P.L) (h : ((X : K⟦X⟧) ^ e) ^ n • w = (l : K) ^ b • z) :
    ∃ z' ∈ P.L, w = (l : K) ^ b • z' := by
  have hc : (l : K) ^ b ≠ 0 := pow_ne_zero _ (l_ne_zero l)
  refine ⟨((l : K) ^ b)⁻¹ • w, mem_tot.2 fun τ => P.mem_extc_iff.2 fun i => ?_,
    (smul_inv_smul₀ hc w).symm⟩
  have hm := P.mem_extc_iff.1 (mem_tot.1 hw τ)
  have hm' := P.mem_extc_iff.1 (mem_tot.1 hz τ)
  have hi : X ^ (e * n) * (P.mxInv τ *ᵥ w τ) i = (l : K) ^ b • (P.mxInv τ *ᵥ z τ) i := by
    have hτ := congrArg (fun v : Vec K a ι => (P.mxInv τ *ᵥ v τ) i) h
    simp only [Pi.smul_apply, Matrix.mulVec_smul, smul_eq_mul] at hτ
    rw [pow_mul]
    exact hτ
  rw [mem_A]
  intro k
  rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, coeff_smul, smul_eq_mul,
    inv_mul_coeff_eq_of_X_pow_mul hc hi]
  exact mem_A.1 (hm' i) _

end GlobalTheory.CokerL
end

