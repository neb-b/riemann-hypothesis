module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0233
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0234
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredModuleFiniteOfGraded
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LenDev

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem finite_mid [IsNoetherianRing R] {M₁ M₂ M₃ : Type 1} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (e : Function.Exact f g)
    [Module.Finite R M₁] [Module.Finite R M₃] : Module.Finite R M₂ := by
  have h₁ : Module.Finite R (LinearMap.ker g) := by
    rw [LinearMap.exact_iff.1 e]
    exact Module.Finite.range f
  have h₂ : Module.Finite R (M₂ ⧸ LinearMap.ker g) :=
    Module.Finite.equiv g.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker g)

theorem H_subsingleton (F : C ⥤ ModuleCat.{0} R) (h : ∀ T, Subsingleton (F.obj T)) (n : ℕ) :
    Subsingleton (CH.H F n) := by
  have hX : Subsingleton ((CH.cx F).X n) := ⟨fun a b => funext fun s => (h _).elim _ _⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).1 x
  obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).1 y
  have e : a = b := hX.elim _ _
  subst e
  rfl

theorem sqM_rep (a b : IdF A) (T : C) (x : sqM a b T) :
    ∃ (y : A.obj T) (hy : y ∈ a.S T), x = sqMk a b y hy := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  exact ⟨y, hy, rfl⟩

theorem sq_self_subsingleton (a : IdF A) (T : C) : Subsingleton ((sq a a).obj T) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x', hx, rfl⟩ := sqM_rep a a T x
  obtain ⟨y', hy, rfl⟩ := sqM_rep a a T y
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ x' = Ideal.Quotient.mk _ y'
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hx, Ideal.Quotient.eq_zero_iff_mem.2 hy]

variable {a b c : IdF A}

theorem sq_inj (hba : ∀ T, b.S T ≤ a.S T) (T : C) :
    Function.Injective ((sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).τ T) := by
  intro x y h
  obtain ⟨x', hx, rfl⟩ := sqM_rep b c T x
  obtain ⟨y', hy, rfl⟩ := sqM_rep b c T y
  have h' := congrArg (fun z : sqM a c T => z.1) h
  exact Subtype.ext h'

theorem sq_exact (hba : ∀ T, b.S T ≤ a.S T) (hcb : ∀ T, c.S T ≤ b.S T) (T : C) :
    Function.Exact ((sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).τ T)
      ((sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).τ T) := by
  intro x
  obtain ⟨x', hx, rfl⟩ := sqM_rep a c T x
  constructor
  · intro h
    have h' : (Ideal.Quotient.mk (b.S T) x') = 0 := congrArg Subtype.val h
    exact ⟨sqMk b c x' (Ideal.Quotient.eq_zero_iff_mem.1 h'), rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨y', hy', rfl⟩ := sqM_rep b c T y
    have e : (Ideal.Quotient.mk (c.S T) y') = Ideal.Quotient.mk (c.S T) x' := congrArg Subtype.val hy
    refine Subtype.ext ?_
    change Ideal.Quotient.mk (b.S T) x' = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have := Ideal.Quotient.eq.1 e
    have h2 := hcb T this
    have h3 := (b.S T).sub_mem hy' h2
    simpa using h3

theorem sq_surj (hcb : ∀ T, c.S T ≤ b.S T) (T : C) :
    Function.Surjective ((sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).τ T) := by
  intro x
  obtain ⟨x', hx, rfl⟩ := sqM_rep a b T x
  exact ⟨sqMk a c x' hx, rfl⟩

theorem sq_les (hba : ∀ T, b.S T ≤ a.S T) (hcb : ∀ T, c.S T ≤ b.S T) (n : ℕ) :
    Function.Exact ((sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).pull n)
      ((sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).pull n) := by
  obtain ⟨δ, -, -, e, -⟩ := CrystallineSemistableComparison.P.les
    (sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).hom
    (sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).hom
    (fun n x y h => funext fun s => sq_inj hba _ (congrFun h s))
    (fun n y => ⟨fun hy => ⟨fun s => ((sq_exact hba hcb _ (y s)).1 (congrFun hy s)).choose,
        funext fun s => ((sq_exact hba hcb _ (y s)).1 (congrFun hy s)).choose_spec⟩, by
      rintro ⟨x, rfl⟩
      funext s
      exact (sq_exact hba hcb _ _).2 ⟨_, rfl⟩⟩)
    (fun n y => ⟨fun s => (sq_surj hcb _ (y s)).choose, funext fun s => (sq_surj hcb _ (y s)).choose_spec⟩)
  exact e n

theorem finite_dev [IsNoetherianRing R] (a : ℕ → IdF A) (hanti : ∀ k l, k ≤ l → ∀ T, (a l).S T ≤ (a k).S T) (s n : ℕ)
    (hgr : ∀ r, r < s → Module.Finite R (CH.H (sq (a r) (a (r + 1))) n)) :
    ∀ (d r : ℕ), r + d = s → Module.Finite R (CH.H (sq (a r) (a s)) n) := by
  intro d
  induction d with
  | zero =>
    intro r h
    obtain rfl : r = s := by omega
    have := H_subsingleton _ (sq_self_subsingleton (a r)) n
    exact Module.Finite.of_finite
  | succ d ih =>
    intro r h
    have := ih (r + 1) (by omega)
    have := hgr r (by omega)
    exact finite_mid _ _ (sq_les (hanti r (r + 1) (by omega)) (hanti (r + 1) s (by omega)) n)

theorem finite_H_sq : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (Fil : ℤ → IdF A),
    (∀ r r' : ℤ, r ≤ r' → ∀ T, (Fil r').S T ≤ (Fil r).S T) → ∀ s : ℕ,
    (∀ r : ℕ, r < s → ∀ j, Module.Finite R (CH.H (sq (Fil r) (Fil ((r : ℤ) + 1))) j)) →
    ∀ j, Module.Finite R (CH.H (sq (Fil 0) (Fil s)) j) := by
  intro R _ _ C _ A Fil hanti s hgr j
  have key := finite_dev (fun r : ℕ => Fil (r : ℤ))
    (fun k l h T => hanti _ _ (by exact_mod_cast h) T) s j
    (fun r hr => by
      have h := hgr r hr j
      rw [← Nat.cast_succ] at h
      exact h) s 0 (by omega)
  beta_reduce at key
  rw [Nat.cast_zero] at key
  exact key

end GlobalTheory.CompanionTheory.LenDev
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthWittCohomology
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LevelOne

universe w w'

theorem mapH_injective {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K : Cx.{w} R} {L : Cx.{w'} R'}
    (φ : Cx.Hom K L σ) (hi : ∀ n, Function.Injective (φ.f n)) (hs : ∀ n, Function.Surjective (φ.f n)) (n : ℕ) :
    Function.Injective (φ.mapH n) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h0 : φ.mapZ n z ∈ (L.B n).submoduleOf (L.Z n) := (Submodule.Quotient.mk_eq_zero _).1 hx
  have h1 : φ.f n z.1 ∈ L.B n := h0
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  change z.1 ∈ K.B n
  cases n with
  | zero =>
    have h2 : φ.f 0 z.1 = 0 := h1
    exact hi 0 (h2.trans (map_zero _).symm)
  | succ n =>
    obtain ⟨w, hw⟩ := h1
    obtain ⟨w', rfl⟩ := hs n w
    rw [φ.comm] at hw
    exact ⟨w', hi _ hw⟩

theorem isNoetherian_of_surj {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (h : Function.Surjective (algebraMap R S)) [IsNoetherian S M] : IsNoetherian R M := by
  let f : Submodule R M →o Submodule S M :=
    { toFun := fun N =>
        { carrier := N
          add_mem' := N.add_mem
          zero_mem' := N.zero_mem
          smul_mem' := fun c x hx => by
            obtain ⟨r, rfl⟩ := h c
            rw [algebraMap_smul]
            exact N.smul_mem r hx }
      monotone' := fun _ _ h => h }
  have hf : StrictMono f := Monotone.strictMono_of_injective f.monotone fun N N' e => by
    ext x
    exact iff_of_eq (congrArg (fun P : Submodule S M => x ∈ P) e)
  rw [isNoetherian_iff']
  exact hf.wellFoundedGT

section Witt

variable (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l]

theorem span_l_isMaximal : (Ideal.span {(l : WittVector l k) ^ 1}).IsMaximal := by
  have e : Ideal.span {(l : WittVector l k) ^ 1} = RingHom.ker (WittVector.constantCoeff (p := l) (R := k)) := by
    ext x
    rw [pow_one, WittVector.mem_span_p_iff_coeff_zero_eq_zero, RingHom.mem_ker, WittVector.constantCoeff_apply]
  rw [e]
  exact RingHom.ker_isMaximal_of_surjective _ (WittVector.constantCoeff_surjective l)

theorem wm_artinian : IsArtinianRing (Wc.Wm l k 1) := by
  haveI := span_l_isMaximal l k
  letI := Ideal.Quotient.field (Ideal.span {(l : WittVector l k) ^ 1})
  infer_instance

end Witt

section Site

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
  (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k)

abbrev QAll : ObjectProperty (Thick (nlFun (Wc.pd l k 1) l X q ((Wc.res l k 1).comp ρ))) :=
  St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ {⊤}

theorem qAll_all (T : Thick (nlFun (Wc.pd l k 1) l X q ((Wc.res l k 1).comp ρ))) : QAll q ρ T :=
  ⟨trivial, ⊤, rfl, fun _ _ => trivial⟩

def toAll : CH.Mor (Wc.OM l (B.schFn q) ρ 1) (CH.modF (sP (QAll q ρ)).A) (Ideal.Quotient.mk _) where
  G := (QAll q ρ).ι
  τ T := { toFun := fun z => z, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  nat _ _ := rfl

theorem toAll_inj (n : ℕ) : Function.Injective ((toAll q ρ).hom.f n) := by
  intro f f' h
  funext s
  exact congrFun h (s ⋙ (QAll q ρ).lift (𝟭 _) (qAll_all q ρ))

theorem toAll_surj (n : ℕ) : Function.Surjective ((toAll q ρ).hom.f n) := by
  intro g
  exact ⟨fun s => g (s ⋙ (QAll q ρ).lift (𝟭 _) (qAll_all q ρ)), rfl⟩

theorem toAll_pull_inj (j : ℕ) : Function.Injective ((toAll q ρ).pull j) :=
  mapH_injective _ (toAll_inj q ρ) (toAll_surj q ρ) j

end Site

theorem finiteLength_level_one : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (j : ℕ),
    Module.Finite (Wc.Wm l k 1) (HO (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ {⊤}) j) →
    IsFiniteLength (WittVector l k) (CH.H (Wc.OM l (B.schFn q) ρ 1) j) := by
  intro l _ k _ _ _ O _ X q ρ j hfin
  haveI := wm_artinian l k
  letI : Module (WittVector l k) (HO (QAll q ρ) j) := Module.compHom _ (algebraMap (WittVector l k) (Wc.Wm l k 1))
  haveI : IsScalarTower (WittVector l k) (Wc.Wm l k 1) (HO (QAll q ρ) j) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hsurj : Function.Surjective (algebraMap (WittVector l k) (Wc.Wm l k 1)) := Ideal.Quotient.mk_surjective
  haveI : IsNoetherian (Wc.Wm l k 1) (HO (QAll q ρ) j) := inferInstance
  haveI : IsArtinian (Wc.Wm l k 1) (HO (QAll q ρ) j) := inferInstance
  haveI : IsNoetherian (WittVector l k) (HO (QAll q ρ) j) := isNoetherian_of_surj hsurj
  haveI : IsArtinian (WittVector l k) (HO (QAll q ρ) j) := isArtinian_of_surjective_algebraMap hsurj
  let f : CH.H (Wc.OM l (B.schFn q) ρ 1) j →ₗ[WittVector l k] HO (QAll q ρ) j :=
    { toFun := (toAll q ρ).pull j
      map_add' := map_add _
      map_smul' := fun r x => ((toAll q ρ).pull j).map_smulₛₗ r x }
  have hf : Function.Injective f := toAll_pull_inj q ρ j
  exact isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨isNoetherian_of_injective f hf, isArtinian_of_injective f hf⟩

end GlobalTheory.CompanionTheory.LevelOne
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GammaComp
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThetaEx

section Gen
variable {O : Type} [CommRing O] {F : Fn O} {d : ℕ} (s : F.Small d) {b : Base} (ht : b.t = 1)
  {κ : O →+* b.R ⧸ b.I}
  (𝓛 : Lift s.a (fun k => (s.T k : s.R)) b.R b.I κ) (δ : DividedPowers (b.I.map 𝓛.i))
  (hδ : IsDPMorphism b.γ δ 𝓛.i) (hp : b.p ≠ 0) (hn : IsNilpotent (b.p : b.R))

theorem arrow_ex (T : Thick (F.cr b ht κ)) (g' : s.R →+* T.B ⧸ T.J)
    (hg' : F.Pt.map (CommRingCat.ofHom g') s.y₀ = T.y.1.2) (u : Fin d → T.B)
    (hu : ∀ k, Ideal.Quotient.mk T.J (u k) = g' (s.T k)) :
    ∃ c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T, ∀ k, c.φ (𝓛.t k) = u k := by
  obtain ⟨g, -, hg, hU⟩ := GlobalTheory.CompanionTheory.ThickHom.main s ht 𝓛 δ hδ hp hn T
  obtain ⟨g₀, -, h₀⟩ := s.univ (CommRingCat.of (T.B ⧸ T.J)) T.y.1.2 (T.y.1.1.comp κ) T.y.2
  have e : g' = g := (h₀ g' hg').trans (h₀ g hg).symm
  subst e
  exact (hU u hu).exists

theorem arrow_uniq (T : Thick (F.cr b ht κ)) (c c' : liftObj s ht 𝓛 δ hδ hp hn ⟶ T)
    (h : ∀ k, c.φ (𝓛.t k) = c'.φ (𝓛.t k)) : c = c' := by
  obtain ⟨g, hc, -, hU⟩ := GlobalTheory.CompanionTheory.ThickHom.main s ht 𝓛 δ hδ hp hn T
  exact (hU (fun k => c'.φ (𝓛.t k)) (fun k => hc c' _ _ (𝓛.hT k).symm)).unique h fun _ => rfl

end Gen

theorem gamma_comp {C C₀ : Type*} [Category C] [Category C₀] {j : C₀ ⥤ C} {U : UF C} {d : ℕ} {D T : C}
    (A : Act j U d D) (a : Gam d) (θ : D ⟶ T) :
    (A.γ a).asHom ≫ θ = A.act (fun k => U.q T ^ (Multiplicative.toAdd a k)) θ := by
  change A.act _ (𝟙 D) ≫ θ = _
  rw [A.act_comp, Category.id_comp]
  congr 1
  funext k
  rw [map_pow, U.map_q]

theorem i_qU {l : ℕ} [Fact l.Prime] (ε : Eps l) (A : PAlg l) (n : ℕ) :
    mapAcr A.fromBase n (ε.qU n : (base l).Acr n) = A.toAcr n (WittVector.teichmuller l (A.s (ε.e 0))) := by
  rw [ε.qU_val, mapAcr_cris, ε.cris_qk]

theorem teich_step {l : ℕ} [Fact l.Prime] (A : PAlg l) (f : A ⟶ A) (n m : ℕ) (e c : A.A)
    (h : Hom.f f c = e ^ m * c) :
    A.toAcr n (WittVector.teichmuller l e) ^ m * A.toAcr n (WittVector.teichmuller l c) =
      mapAcr f n (A.toAcr n (WittVector.teichmuller l c)) := by
  rw [mapAcr_toAcr, mapW, WittVector.map_teichmuller, h, map_mul, map_pow, map_mul, map_pow]

theorem main : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (k : Bool) (n : ℕ) (𝓛 : Lift s.a (fun k => (s.T k : s.R)) (bs l k n).R (bs l k n).I (κb κ k n)) (δ : DividedPowers ((bs l k n).I.map 𝓛.i)) (hδ : IsDPMorphism (bs l k n).γ δ 𝓛.i) (hp : (bs l k n).p ≠ 0) (hn : IsNilpotent ((bs l k n).p : (bs l k n).R)) (ε : Eps l) (A : Act (𝟭 _) (thU (Lc F κ k n) (ε.qU n) (ε.qU_mem k n)) d (liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn)) (A' : Act (jE (F.pt κ)) (epsU ε (F.pt κ)) d 𝒯.obj), (∀ (T : Thick (Lc F κ k n)) (a : Fin d → (thU (Lc F κ k n) (ε.qU n) (ε.qU_mem k n)).U T) (c : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ T) (j : Fin d), (A.act a c).φ (𝓛.t j) = ((a j).1 : T.B) * c.φ (𝓛.t j)) → (∀ (T : (F.pt κ).Elements) (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (j : Fin d), PAlg.Hom.f (A'.act a φ).hom (𝒯.c j 0).val = ((a j).1 : T.1.A) * PAlg.Hom.f φ.hom (𝒯.c j 0).val) → ∃ θ : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ (gE F κ k n).obj 𝒯.obj, (∀ j, θ.φ (𝓛.t j) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) ∧ ∀ a, (A.γ a).asHom ≫ θ = θ ≫ (gE F κ k n).map (A'.γ a).asHom := by
  intro l _ O _ F κ d s 𝒯 k n 𝓛 δ hδ hp hn ε A A' hA hA'
  have hy : F.Pt.map (CommRingCat.ofHom ((uJ k 𝒯.A n).comp 𝒯.g)) s.y₀ = ((gE F κ k n).obj 𝒯.obj).y.1.2 := by
    rw [CommRingCat.ofHom_comp, F.Pt.map_comp]
    rfl
  have hu : ∀ j, Ideal.Quotient.mk (JJ k 𝒯.A n) (𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) =
      (uJ k 𝒯.A n).comp 𝒯.g (s.T j) := fun j => by
    rw [RingHom.comp_apply, ← 𝒯.c_sharp j]
    exact (uJ_th k 𝒯.A n _).symm
  obtain ⟨θ, hθ⟩ := arrow_ex s rfl 𝓛 δ hδ hp hn ((gE F κ k n).obj 𝒯.obj) ((uJ k 𝒯.A n).comp 𝒯.g) hy
    (fun j => 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) hu
  refine ⟨θ, hθ, fun a => arrow_uniq s rfl 𝓛 δ hδ hp hn _ _ _ fun j => ?_⟩
  have h1 : ((A.γ a).asHom ≫ θ).φ (𝓛.t j) =
      𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.A.s (ε.e 0))) ^ (Multiplicative.toAdd a j) *
        𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A)) := by
    rw [gamma_comp A a θ, hA _ _ θ j, hθ j, ← i_qU]
    rfl
  have h2 : PAlg.Hom.f (A'.γ a).asHom.hom (𝒯.c j 0).val =
      (𝒯.A.s (ε.e 0)) ^ (Multiplicative.toAdd a j) * (𝒯.c j 0).val := hA' 𝒯.obj _ (𝟙 𝒯.obj) j
  have h3 : (θ ≫ (gE F κ k n).map (A'.γ a).asHom).φ (𝓛.t j) =
      mapAcr (A'.γ a).asHom.hom n (𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) :=
    congrArg (mapAcr (A'.γ a).asHom.hom n) (hθ j)
  rw [h1, h3]
  exact teich_step 𝒯.A _ n _ _ _ h2

end GlobalTheory.CompanionTheory.ThetaEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentRefinementOfUnimodular
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.TestCover

section Ring

variable {S : Type*} [CommRing S]

theorem mem_of_compare {f g d : S} (h : Ideal.span {f, g} = ⊤) (h1 : d * f ∈ Ideal.span {g})
    (h2 : (1 - d) * g ∈ Ideal.span {f}) : d ∈ Ideal.span {g} ∧ 1 - d ∈ Ideal.span {f} := by
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.1 (Ideal.eq_top_iff_one _ |>.1 h)
  constructor
  · have e : d = x * (d * f) + (d * y) * g := by
      linear_combination (-d) * hxy
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1)
      (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g))
  · have e : 1 - d = ((1 - d) * x) * f + y * ((1 - d) * g) := by
      linear_combination (-(1 - d)) * hxy
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f))
      (Ideal.mul_mem_left _ _ h2)

theorem idem_prod {ι : Type*} (t : Finset ι) (f : ι → S) (h : ∀ k, IsIdempotentElem (f k)) :
    IsIdempotentElem (∏ k ∈ t, f k) := by
  unfold IsIdempotentElem
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => h k

theorem span_top_of_prod {m : ℕ} (e : Fin m → S) (h : ∏ k, (1 - e k) = 0) :
    Ideal.span (Set.range e) = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← Ideal.Quotient.eq_zero_iff_mem]
  have hk : ∀ k, Ideal.Quotient.mk (Ideal.span (Set.range e)) (1 - e k) = 1 := fun k => by
    have h0 : Ideal.Quotient.mk (Ideal.span (Set.range e)) (e k) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self k))
    rw [map_sub, map_one, h0, sub_zero]
  have := congrArg (Ideal.Quotient.mk (Ideal.span (Set.range e))) h
  rw [map_prod, Finset.prod_congr rfl fun k _ => hk k, Finset.prod_const_one, map_zero] at this
  rw [map_one, this]

theorem idem_refine
    (hV : ∀ f g : S, Ideal.span {f, g} = ⊤ →
      ∃ e : S, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f}) :
    ∀ (m : ℕ) (s : Fin m → S) (c : S), IsIdempotentElem c → c ∈ Ideal.span (Set.range s) →
      ∃ e : Fin m → S, (∀ k, IsIdempotentElem (e k)) ∧ (∀ k, e k ∈ Ideal.span {s k}) ∧
        c * ∏ k, (1 - e k) = 0 := by
  intro m
  induction m with
  | zero =>
    intro s c _ hc
    have h0 : c = 0 := by
      rw [Set.range_eq_empty, Ideal.span_empty] at hc
      exact (Submodule.mem_bot _).1 hc
    exact ⟨Fin.elim0, fun k => k.elim0, fun k => k.elim0, by rw [h0, zero_mul]⟩
  | succ m ih =>
    intro s c hc hcs
    have hr : Set.range s = insert (s 0) (Set.range (Fin.tail s)) := by
      conv_lhs => rw [← Fin.cons_self_tail s]
      exact Fin.range_cons _ _
    rw [hr, Ideal.mem_span_insert] at hcs
    obtain ⟨a, r, hr', hcr⟩ := hcs
    have htop : Ideal.span {s 0, r + (1 - c)} = ⊤ := by
      rw [Ideal.eq_top_iff_one, Ideal.mem_span_pair]
      exact ⟨a, 1, by linear_combination -hcr⟩
    obtain ⟨d, hd, h1, h2⟩ := hV _ _ htop
    obtain ⟨hdg, hds⟩ := mem_of_compare htop h1 h2
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hdg
    have hcc : c * c = c := hc
    have hcd : IsIdempotentElem (c * d) := hc.mul hd
    have hmem : c * d ∈ Ideal.span (Set.range (Fin.tail s)) := by
      have e : c * d = (t * c) * r := by
        rw [← ht]
        linear_combination (-t) * hcc
      rw [e]
      exact Ideal.mul_mem_left _ _ hr'
    obtain ⟨e', hi, hm, hp⟩ := ih (Fin.tail s) (c * d) hcd hmem
    refine ⟨Fin.cons (1 - d) e', ?_, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun i => ?_) k
      · simpa using hd.one_sub
      · simpa using hi i
    · intro k
      refine Fin.cases ?_ (fun i => ?_) k
      · simpa using hds
      · simpa [Fin.tail] using hm i
    · rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      linear_combination hp

end Ring

theorem test_cover : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.IsTest → ∀ {m : ℕ} (s : Fin m → A.U),
    Ideal.span (Set.range s) = ⊤ → ∃ e : Fin m → A.A, (∀ k, IsIdempotentElem (e k)) ∧
      Ideal.span (Set.range e) = ⊤ ∧ ∀ k, A.sharp (e k) ∈ Ideal.span {s k} := by
  intro l _ A hA m s hs
  have hV : ∀ f g : A.U, Ideal.span {f, g} = ⊤ →
      ∃ e : A.U, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f} :=
    fun f g h => hA.val_aic.1 f g ⟨0, by rw [pow_zero, h]; trivial⟩
  obtain ⟨u, hi, hm, hp⟩ := idem_refine hV m s 1 IsIdempotentElem.one (by rw [hs]; trivial)
  rw [one_mul] at hp
  have hex : ∀ k, ∃ e₀ : A.A, IsIdempotentElem e₀ ∧ A.sharp e₀ = u k := fun k =>
    (RL.idem_au A (u k) (hi k)).exists
  choose e he hsh using hex
  have hc := (RL.sharp_cong A).2.2
  have hzero : A.sharp 0 = 0 := by
    have := hc 1 IsIdempotentElem.one
    rwa [sub_self, map_one, sub_self] at this
  have hsp : A.sharp (∏ k, (1 - e k)) = 0 := by
    rw [map_prod, ← hp]
    exact Finset.prod_congr rfl fun k _ => by rw [hc _ (he k), hsh]
  have hidem : IsIdempotentElem (∏ k, (1 - e k)) :=
    idem_prod _ _ fun k => (he k).one_sub
  have h0 : ∏ k, (1 - e k) = 0 :=
    (RL.idem_au A 0 IsIdempotentElem.zero).unique ⟨hidem, hsp⟩ ⟨IsIdempotentElem.zero, hzero⟩
  exact ⟨e, he, span_top_of_prod e h0, fun k => by rw [hsh]; exact hm k⟩

end GlobalTheory.CompanionTheory.TestCover
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterInducedTiedSixStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_induced_tied_six : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied6 l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ)
      (J : (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ),
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ J → PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ⁻¹ (-J) := by
  first | exact @GlobalTheory.CompanionTheory.DeRhamChar.isdRJ_inv | exact GlobalTheory.CompanionTheory.DeRhamChar.isdRJ_inv | (intros; apply GlobalTheory.CompanionTheory.DeRhamChar.isdRJ_inv <;> assumption)
end
end

