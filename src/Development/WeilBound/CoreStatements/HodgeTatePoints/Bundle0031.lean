module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0010
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0023
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import ReciprocityTheory.DualLattices.PowMemCarrier
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0016

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLPullEq
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LPullEq

theorem pull_eq_pullLoc_of_dominates : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ]
    (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (X' : Scheme.{0}) (Ω' : Type)
    [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (F : Type) [AddCommGroup F] [Module Ω' F]
    (j : E →+ F) (f : X' ⟶ M.X), L.IsCohOn Set.univ → Dominates ξ' M.ξ f i →
      L.pull ξ' f j = L.pullLoc ξ' i j ∧ ∀ p', p' ∈ ctrSet o x i ξ' := by
  intro o _ Ω _ _ κ _ x M E _ _ L X' Ω' _ ξ' i F _ _ j f hL hd
  have dl := PositivityTheory.HtPt.Mb.dom_local M.X Ω M.ξ X' Ω' ξ' i f hd
  refine ⟨?_, fun p' => ?_⟩
  · funext p'
    obtain ⟨h, hc⟩ := dl p'
    rw [PositivityTheory.HtPt.Mb.pullloc_centre o Ω κ x M E L X' Ω' ξ' i F j ⟨f p'.1, h⟩ p' hL hc]
    unfold Lat.pull
    congr 1
    ext e'
    constructor
    · rintro ⟨_, e, he, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨h, e, he, rfl⟩
  · obtain ⟨h, h1, -⟩ := dl p'
    obtain ⟨c, hc⟩ := M.tie.cover ⟨f p'.1, h⟩
    exact ⟨c, hc.1, fun a ha => h1 a (((M.tie.ring c hc.1) a).1 ha _ hc)⟩

end PositivityTheory.HtPt.Mb.LPullEq


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.pull_eq : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (F : Type) [AddCommGroup F] [Module Ω' F] (j : E →+ F) (f : X' ⟶ M.X), L.IsCohOn Set.univ → Dominates ξ' M.ξ f i → L.pull ξ' f j = L.pullLoc ξ' i j ∧ ∀ p', p' ∈ ctrSet o x i ξ' :=
  @PositivityTheory.HtPt.Mb.LPullEq.pull_eq_pullLoc_of_dominates
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RangeSubtypeEq
section
noncomputable section

namespace PositivityTheory.HtPt.Rc

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

section Gen

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X N Q : Type} [AddCommGroup X] [AddCommGroup N] [AddCommGroup Q]

lemma map_res_eq (M : Submodule R (N → C)) (ι : X →+ N) (K : AddSubgroup N) (e : X ≃+ K)
    (he : ∀ x, (e x : N) = ι x) :
    M.map (LinearMap.funLeft R C ι) =
      (M.map (resK (R := R) K)).map (pbE (C := C) (R := R) e : (K → C) →ₗ[R] (X → C)) := by
  rw [← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro g
  funext x
  show g (ι x) = g (e x)
  rw [he]

lemma comap_quo_eq (M : Submodule R (N → C)) (ψ : N →+ Q) (K : AddSubgroup N) (e : Q ≃+ N ⧸ K)
    (he : ∀ x, e (ψ x) = (x : N ⧸ K)) :
    M.comap (LinearMap.funLeft R C ψ) =
      (M.comap (pullQ (R := R) K)).map (pbE (C := C) (R := R) e : (N ⧸ K → C) →ₗ[R] (Q → C)) := by
  ext g
  rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
  have : pullQ (R := R) K ((pbE (C := C) (R := R) e).symm g) = LinearMap.funLeft R C ψ g := by
    funext x
    show (pbE (C := C) (R := R) e).symm g (x : N ⧸ K) = g (ψ x)
    rw [LinearEquiv.funCongrLeft_symm]
    show g (e.symm (x : N ⧸ K)) = g (ψ x)
    rw [← he, AddEquiv.symm_apply_apply]
  rw [this]

lemma exists_subEquiv (ι : X →+ N) (hι : Function.Injective ι) (K : AddSubgroup N)
    (hK : ι.range = K) : ∃ e : X ≃+ K, ∀ x, (e x : N) = ι x := by
  subst hK
  exact ⟨AddMonoidHom.ofInjective hι, fun _ => rfl⟩

lemma exists_quoEquiv (ψ : N →+ Q) (hψ : Function.Surjective ψ) (K : AddSubgroup N)
    (hK : K = ψ.ker) : ∃ e : Q ≃+ N ⧸ K, ∀ x, e (ψ x) = (x : N ⧸ K) := by
  subst hK
  refine ⟨(QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ).symm, fun x => ?_⟩
  rw [AddEquiv.symm_apply_eq]
  rfl

lemma invFun_eq (M : Submodule R (N → C)) (ψ : N →+ Q) (hψ : Function.Surjective ψ)
    (K : AddSubgroup N) (hK : ∀ x, x ∈ K ↔ ψ x = 0) :
    invFun M K = (M.comap (LinearMap.funLeft R C ψ)).map (LinearMap.funLeft R C ψ) := by
  ext g
  constructor
  · rintro ⟨hg, hinv⟩
    have h : LinearMap.funLeft R C ψ (fun c => g (Function.surjInv hψ c)) = g := by
      funext x
      show g (Function.surjInv hψ (ψ x)) = g x
      have hk : Function.surjInv hψ (ψ x) - x ∈ K := by
        rw [hK, map_sub, Function.surjInv_eq hψ, sub_self]
      have := hinv x _ hk
      rwa [add_sub_cancel] at this
    exact ⟨_, by show LinearMap.funLeft R C ψ _ ∈ M; rw [h]; exact hg, h⟩
  · rintro ⟨q, hq, rfl⟩
    refine ⟨hq, fun x k hk => ?_⟩
    show q (ψ (x + k)) = q (ψ x)
    rw [map_add (f := _), (hK k).1 hk, add_zero]

lemma aug_pull (φ : X →+ N) (M : Submodule R (N → C)) (M' : Submodule R (X → C))
    (h : ∀ g ∈ M, LinearMap.funLeft R C φ g ∈ M') {g : N → C} (hg : g ∈ augIdeal M) :
    LinearMap.funLeft R C φ g ∈ augIdeal M' := by
  rw [mem_aug] at hg ⊢
  refine ⟨h g hg.1, ?_⟩
  show g (φ 0) = 0
  rw [map_zero, hg.2]

lemma sq_pull (φ : X →+ N) (M : Submodule R (N → C)) (M' : Submodule R (X → C))
    (h : ∀ g ∈ M, LinearMap.funLeft R C φ g ∈ M') {g : N → C} (hg : g ∈ sqIdeal (augIdeal M)) :
    LinearMap.funLeft R C φ g ∈ sqIdeal (augIdeal M') := by
  have h' : (sqIdeal (augIdeal M)).map (LinearMap.funLeft R C φ) ≤ sqIdeal (augIdeal M') := by
    rw [sqIdeal, Submodule.map_span_le]
    rintro s ⟨f, hf, f', hf', rfl⟩
    exact Submodule.subset_span ⟨_, aug_pull φ M M' h hf, _, aug_pull φ M M' h hf', rfl⟩
  exact h' (Submodule.mem_map_of_mem hg)

variable {v : Valuation C NNReal}

theorem exists_res (hv : v.Integers R) [Fintype N] [DecidableEq N] [Fintype X] [DecidableEq X]
    (AA : HopfOrder (C := C) R N) (ι : X →+ N) (hι : Function.Injective ι) :
    ∃ AK : HopfOrder (C := C) R X, AK.carrier = AA.carrier.map (LinearMap.funLeft R C ι) := by
  classical
  obtain ⟨K, hK⟩ : ∃ K, ι.range = K := ⟨_, rfl⟩
  obtain ⟨e, he⟩ := exists_subEquiv ι hι K hK
  have : Fintype (N ⧸ K) := Fintype.ofFinite _
  obtain ⟨⟨AK, hAK⟩, -⟩ := ReciprocityTheory.PGsh.L2.h2 C R v hv N K AA
  refine ⟨hopfPull e AK, ?_⟩
  rw [map_res_eq _ ι _ e he, ← hAK]
  rfl

theorem exists_quo (hv : v.Integers R) [Fintype N] [DecidableEq N] [Fintype Q] [DecidableEq Q]
    (AA : HopfOrder (C := C) R N) (ψ : N →+ Q) (hψ : Function.Surjective ψ) :
    ∃ AQ : HopfOrder (C := C) R Q, AQ.carrier = AA.carrier.comap (LinearMap.funLeft R C ψ) := by
  classical
  obtain ⟨e, he⟩ := exists_quoEquiv ψ hψ ψ.ker rfl
  have : Fintype (N ⧸ ψ.ker) := Fintype.ofFinite _
  obtain ⟨-, ⟨AQ, hAQ⟩, -⟩ := ReciprocityTheory.PGsh.L2.h2 C R v hv N ψ.ker AA
  refine ⟨hopfPull e AQ, ?_⟩
  rw [comap_quo_eq _ ψ _ e he, ← hAQ]
  rfl

theorem colen_ses [IsAlgClosed C] [CharZero C] (hv : v.Integers R) [Fintype N] [DecidableEq N]
    [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    (AA : HopfOrder (C := C) R N) (ι : X →+ N) (hι : Function.Injective ι)
    (ψ : N →+ Q) (hψ : Function.Surjective ψ) (hex : ι.range = ψ.ker) (c cQ cK : NNReal)
    (hc : HasColen R v AA.carrier c)
    (hQ : HasColen R v (AA.carrier.comap (LinearMap.funLeft R C ψ)) cQ)
    (hK : HasColen R v (AA.carrier.map (LinearMap.funLeft R C ι)) cK) :
    c = cQ ^ Fintype.card X * cK ^ Fintype.card Q := by
  classical
  obtain ⟨K, hKd⟩ : ∃ K, ι.range = K := ⟨_, rfl⟩
  obtain ⟨e, he⟩ := exists_subEquiv ι hι K hKd
  obtain ⟨e', he'⟩ := exists_quoEquiv ψ hψ K (hKd ▸ hex)
  have : Fintype (N ⧸ K) := Fintype.ofFinite _
  obtain ⟨-, -, h3iii, -⟩ := ReciprocityTheory.PGsh.L2.h3 C R inferInstance inferInstance v hv N K AA
  rw [map_res_eq _ ι _ e he] at hK
  rw [comap_quo_eq _ ψ _ e' he'] at hQ
  have hK' := hasColen_map v e.symm _ _ hK
  have hQ' := hasColen_map v e'.symm _ _ hQ
  rw [map_pbE_symm] at hK' hQ'
  rw [Fintype.card_congr e.toEquiv, Fintype.card_congr e'.toEquiv]
  exact h3iii c cQ cK hc hQ' hK'

theorem om_exact [IsAlgClosed C] [CharZero C] (hv : v.Integers R) [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) (ι : X →+ N)
    (ψ : N →+ Q) (hψ : Function.Surjective ψ) (hι : Function.Injective ι) (hex : ι.range = ψ.ker)
    (g : N → C) (hg : g ∈ augIdeal AA.carrier)
    (hr : LinearMap.funLeft R C ι g ∈
      sqIdeal (augIdeal (AA.carrier.map (LinearMap.funLeft R C ι)))) :
    ∃ b ∈ augIdeal (AA.carrier.comap (LinearMap.funLeft R C ψ)),
      g - LinearMap.funLeft R C ψ b ∈ sqIdeal (augIdeal AA.carrier) := by
  classical
  obtain ⟨e, he⟩ := exists_subEquiv ι hι _ rfl
  obtain ⟨e', he'⟩ := exists_quoEquiv ψ hψ ι.range hex
  have : Fintype (N ⧸ ι.range) := Fintype.ofFinite _
  obtain ⟨-, -, -, h3iv⟩ := ReciprocityTheory.PGsh.L2.h3 C R inferInstance inferInstance v hv N ι.range AA
  have hres : ∀ f : N → C, LinearMap.funLeft R C (e.symm : ι.range →+ X)
      (LinearMap.funLeft R C ι f) = resK (R := R) ι.range f := by
    intro f
    funext k
    show f (ι (e.symm k)) = f k
    rw [← he, AddEquiv.apply_symm_apply]
  have h1 := sq_pull (e.symm : ι.range →+ X) _ (AA.carrier.map (resK (R := R) ι.range))
    (by rintro _ ⟨f, hf, rfl⟩; rw [hres]; exact ⟨f, hf, rfl⟩) hr
  rw [hres, sq_eq_mul] at h1
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 (h3iv g hg h1)
  obtain ⟨b, hb, rfl⟩ := hu
  have hp : ∀ b : N ⧸ ι.range → C, LinearMap.funLeft R C ψ
      (LinearMap.funLeft R C (e' : Q →+ N ⧸ ι.range) b) = pullQ (R := R) ι.range b := by
    intro b
    funext x
    show b (e' (ψ x)) = b x
    rw [he']
  refine ⟨LinearMap.funLeft R C (e' : Q →+ N ⧸ ι.range) b, aug_pull _ _ _ ?_ hb, ?_⟩
  · intro f hf
    show LinearMap.funLeft R C ψ _ ∈ AA.carrier
    rw [hp]
    exact hf
  · rw [hp, ← huw, add_sub_cancel_left, sq_eq_mul]
    exact hw

end Gen

section Scalars

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {F : Type} [Field F]
variable {X N : Type} [AddCommGroup X] [AddCommGroup N] [Module F X] [Module F N]

lemma fstable_map (M : Submodule R (N → C)) (hM : FStable (F := F) M) (ι : X →ₗ[F] N) :
    FStable (F := F) (M.map (LinearMap.funLeft R C ι)) := by
  rintro a _ ⟨g, hg, rfl⟩
  refine ⟨_, hM a g hg, ?_⟩
  funext x
  show g (a • ι x) = g (ι (a • x))
  rw [map_smul]

lemma fstable_comap (M : Submodule R (N → C)) (hM : FStable (F := F) M) (ψ : N →ₗ[F] X) :
    FStable (F := F) (M.comap (LinearMap.funLeft R C ψ)) := by
  intro a g hg
  have := hM a _ hg
  show LinearMap.funLeft R C ψ _ ∈ M
  convert this using 1
  funext x
  show g (a • ψ x) = g (ψ (a • x))
  rw [map_smul]

lemma range_subtype_eq (K : Submodule F N) :
    (K.subtype.toAddMonoidHom).range = (K.mkQ.toAddMonoidHom).ker := by
  ext x
  simp [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]

end Scalars

theorem subquo : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ (K : Submodule F N) [Fintype K] [DecidableEq K] [Fintype (N ⧸ K)] [DecidableEq (N ⧸ K)], (∃ AK : HopfOrder (C := C) R K, AK.carrier = (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) ∧ FStable (F := F) AK.carrier) ∧ (∃ AQ : HopfOrder (C := C) R (N ⧸ K), AQ.carrier = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) ∧ FStable (F := F) AQ.carrier) ∧ invFun AA.carrier K.toAddSubgroup = (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))).map (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K)) ∧ ∀ c cQ cK, HasColen R v AA.carrier c → HasColen R v (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) cQ → HasColen R v (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) cK → c = cQ ^ Fintype.card K * cK ^ Fintype.card (N ⧸ K) := by
  intro p _ C _ _ _ v R _ _ hv _ F _ _ _ _ f _ N _ _ _ _ AA hAA K _ _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨AK, hAK⟩ := exists_res hv AA K.subtype.toAddMonoidHom Subtype.val_injective
    exact ⟨AK, hAK, hAK ▸ fstable_map _ hAA K.subtype⟩
  · obtain ⟨AQ, hAQ⟩ := exists_quo hv AA K.mkQ.toAddMonoidHom K.mkQ_surjective
    exact ⟨AQ, hAQ, hAQ ▸ fstable_comap _ hAA K.mkQ⟩
  · exact invFun_eq _ K.mkQ.toAddMonoidHom K.mkQ_surjective _ (fun x => by simp)
  · intro c cQ cK hc hQ hK
    exact colen_ses hv AA K.subtype.toAddMonoidHom Subtype.val_injective K.mkQ.toAddMonoidHom
      K.mkQ_surjective (range_subtype_eq K) c cQ cK hc hQ hK

end PositivityTheory.HtPt.Rc
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.Twfunct
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Twfunct

section General

variable {R : Type} [CommRing R] [IsDomain R] {S : Scheme.{0}} {G : Over S} [GrpObj G]
  {x : Spec (CommRingCat.of R) ⟶ S}

theorem exists_lift {T T' : Type} [CommGroup T] [CommGroup T'] (Γ : QFGroup R T) (Γ' : QFGroup R T')
    {N N' : ℕ} {i : Γ.G.left ⟶ G.left} {i' : Γ'.G.left ⟶ G.left}
    (h : Γ.IsTorsionAlong G x N i) (h' : Γ'.IsTorsionAlong G x N' i') (hN : N ∣ N')
    (u : G ⟶ G) [IsMonHom u] : ∃ a : Γ.G ⟶ Γ'.G, a.left ≫ i' = i ≫ u.left := by
  let g : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have hg : g ^ N = 1 := (h.kernel Γ.G g).2 ⟨𝟙 _, by simp [g]⟩
  obtain ⟨k, rfl⟩ := hN
  have hg' : (g ≫ u) ^ (N * k) = 1 := by
    rw [← MonObj.pow_comp, pow_mul, hg, one_pow, MonObj.one_comp]
  obtain ⟨a, ha⟩ := (h'.kernel Γ.G (g ≫ u)).1 hg'
  exact ⟨a, by rw [ha]; simp [g]⟩

theorem left_ext {T : Type} [CommGroup T] (Γ : QFGroup R T) {N : ℕ} {i : Γ.G.left ⟶ G.left}
    (h : Γ.IsTorsionAlong G x N i) {Y : Scheme.{0}} (v w : Y ⟶ Γ.G.left) (h1 : v ≫ Γ.G.hom = w ≫ Γ.G.hom)
    (h2 : v ≫ i = w ≫ i) : v = w := by
  have := h.inj (Over.mk (w ≫ Γ.G.hom)) (Over.homMk v h1) (Over.homMk w rfl) h2
  exact congrArg (fun z => z.left) this

omit [IsDomain R] in
theorem valAt_comp {X Y : Scheme.{0}} (v : Spec (CommRingCat.of R) ⟶ X) (a : X ⟶ Y) (s : Γ(Y, ⊤)) :
    valAt v ⊤ le_top ((a.app ⊤).hom s) = valAt (v ≫ a) ⊤ le_top s :=
  Funct.valAt_pullback v a _ rfl ⊤ le_top le_top s

omit [IsDomain R] in
theorem valAt_specMap {B : Type} [CommRing B] {Y : Scheme.{0}} (π : R →+* B) (v : Spec (CommRingCat.of R) ⟶ Y)
    (s : Γ(Y, ⊤)) : valAt (Spec.map (CommRingCat.ofHom π) ≫ v) ⊤ le_top s = π (valAt v ⊤ le_top s) := by
  have h1 : ∀ {Z : Scheme.{0}} (w : Z ⟶ Y), w.appLE ⊤ ⊤ le_top = w.appTop := fun w =>
    w.appLE_eq_app
  simp only [valAt, h1]
  rw [Scheme.Hom.comp_appTop]
  have := congrArg (fun z => z.hom (v.appTop.hom s)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom π))
  exact this

omit [IsDomain R] in
theorem pt_nsmul {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) (e : L) (N : ℕ) :
    M.pt (N • e) = M.pt e ^ N := by
  induction N with
  | zero =>
    have := M.add 0 0
    rw [add_zero] at this
    simpa using (left_eq_mul.1 this)
  | succ k ih => rw [succ_nsmul, M.add, ih, pow_succ]

theorem exists_tan {T : Type} [CommGroup T] (Γ : QFGroup R T) {N : ℕ} {i : Γ.G.left ⟶ G.left}
    (h : Γ.IsTorsionAlong G x N i) {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) (e : L) :
    ∃ v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left,
      v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
        (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧
      v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left := by
  let Q := R ⧸ Ideal.span {(N : R)}
  let q : R →+* Q := Ideal.Quotient.mk _
  let c : R →+* DualNumber Q := (algebraMap Q (DualNumber Q)).comp q
  let Y : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom c))
  have hc : (dualMap q).comp (algebraMap R (DualNumber R)) = c := by
    ext r <;> simp [c, dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let k : Over.mk (Y.hom ≫ x) ⟶ epsAt x := Over.homMk (Spec.map (CommRingCat.ofHom (dualMap q))) (by
    change Spec.map _ ≫ Spec.map _ ≫ x = Spec.map _ ≫ x
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hc])
  let k₀ : Over.mk (Y.hom ≫ x) ⟶ Over.mk x := Over.homMk Y.hom rfl
  have hN : q (N : R) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hc' : (dualMap q).comp (epsMul (N : R)) = c.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    refine RingHom.ext fun r => ?_
    ext <;> simp [c, dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl, -map_natCast, hN]
  have hg : (k ≫ M.pt e) ^ N = 1 := by
    rw [← MonObj.comp_pow, ← pt_nsmul, ← MonObj.comp_one k₀]
    ext1
    rw [Over.comp_left, Over.comp_left, ← Nat.cast_smul_eq_nsmul R, M.smul, ← M.tan e]
    change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ Spec.map _ ≫ _
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hc']
  obtain ⟨v, hv⟩ := (h.kernel Y (k ≫ M.pt e)).1 hg
  exact ⟨v.left, Over.w v, hv⟩

end General

def levMap {La : Type} [AddCommGroup La] (p n : ℕ) (φ : La →+ La) : LevGrp La p n →* LevGrp La p n :=
  AddMonoidHom.toMultiplicative
    (Submodule.mapQ _ _ φ.toIntLinearMap (by
      rintro _ ⟨a, rfl⟩
      exact ⟨φ a, (map_nsmul φ (p ^ n) a).symm⟩)).toAddMonoidHom

theorem levMap_lev {La : Type} [AddCommGroup La] (p n : ℕ) (φ : La →+ La) (a : La) :
    levMap p n φ (lev p n a) = lev p n (φ a) := rfl

theorem lev_surj {La : Type} [AddCommGroup La] (p n : ℕ) (t : LevGrp La p n) : ∃ a, lev p n a = t := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd t)
  exact ⟨a, by simp [lev, ha]⟩

theorem lev_zero {La : Type} [AddCommGroup La] (p n : ℕ) : lev p n (0 : La) = 1 := rfl

theorem finite_lev {La : Type} [AddCommGroup La] [Module.Finite ℤ La] {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    Finite (LevGrp La p n) := by
  have : Finite (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) := by
    refine Module.finite_of_fg_torsion _ fun t => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    refine ⟨⟨((p ^ n : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast pow_ne_zero n hp)⟩, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨a, (natCast_zsmul a (p ^ n)).symm⟩
  infer_instance

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] {S : Scheme.{0}} {G : Over S} [GrpObj G]
  {y : Spec (CommRingCat.of O) ⟶ S} {La : Type} [AddCommGroup La] (X : TorsTower p G y La)
  {L : Type} [AddCommGroup L] [Module O L] (M : LieModel G y L)

theorem isDer_res (n : ℕ) (f : LevGrp La p (n + 1) → O) (g : LevGrp La p n → O) (w : Module.Dual O L)
    (hf : X.IsDer M (n + 1) f w) (hg : ∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) : X.IsDer M n g w := by
  obtain ⟨s, hs, hw⟩ := hf
  obtain ⟨j, hj⟩ := exists_lift (X.Γ n) (X.Γ (n + 1)) (X.tors n) (X.tors (n + 1)) (pow_dvd_pow p n.le_succ) (𝟙 G)
  rw [Over.id_left, Category.comp_id] at hj
  refine ⟨(j.left.app ⊤).hom s, fun t => ?_, fun e => ?_⟩
  · obtain ⟨a, rfl⟩ := lev_surj p n t
    have : ((X.Γ n).pt (lev p n a)).left ≫ j.left = ((X.Γ (n + 1)).pt (lev p (n + 1) (p • a))).left := by
      refine left_ext _ (X.tors (n + 1)) _ _ ?_ ?_
      · rw [Category.assoc, Over.w, Over.w, Over.w]
      · rw [Category.assoc, hj, X.compat]
    rw [valAt_comp, this, hs, hg]
  · obtain ⟨v, hv1, hv2, hv3⟩ := hw e
    obtain ⟨v', h1, h2⟩ := exists_tan (X.Γ n) (X.tors n) M e
    refine ⟨v', h1, h2, ?_⟩
    have hle : Ideal.span {((p ^ (n + 1) : ℕ) : O)} ≤ Ideal.span {((p ^ n : ℕ) : O)} :=
      Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast (pow_dvd_pow p n.le_succ))
    let π := Ideal.Quotient.factor hle
    have : v' ≫ j.left = Spec.map (CommRingCat.ofHom (dualMap π)) ≫ v := by
      refine left_ext _ (X.tors (n + 1)) _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, Over.w, h1, hv1, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        refine RingHom.ext fun r => ?_
        ext <;> simp [π, dualMap, TrivSqZeroExt.algebraMap_eq_inl]
      · rw [Category.assoc, Category.assoc, hj, h2, hv2, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
        congr 3
        refine RingHom.ext fun r => ?_
        ext <;> simp [π, dualMap]
    have h0 : g 1 = f 1 := by simpa [lev_zero] using hg 0
    rw [valAt_comp, this, valAt_specMap, hv3, h0]
    ext <;> simp [π, dualMap]

theorem exists_endo (u : G ⟶ G) [IsMonHom u] (φ : La →+ La) (hu : X.Induces u φ) (n : ℕ) :
    ∃ a : (X.Γ n).G ⟶ (X.Γ n).G, a.left ≫ X.i n = X.i n ≫ u.left ∧
      ∀ t, (X.Γ n).pt t ≫ a = (X.Γ n).pt (levMap p n φ t) := by
  obtain ⟨a, ha⟩ := exists_lift (X.Γ n) (X.Γ n) (X.tors n) (X.tors n) dvd_rfl u
  refine ⟨a, ha, fun t => ?_⟩
  obtain ⟨b, rfl⟩ := lev_surj p n t
  refine (X.tors n).inj _ _ _ ?_
  rw [levMap_lev, hu, Over.comp_left, Category.assoc, ha]

theorem isDer_endo (u : G ⟶ G) [IsMonHom u] (φ : La →+ La) (dφ : L →ₗ[O] L) (hu : X.Induces u φ)
    (hd : M.IsDiffOf u dφ) (n : ℕ) (f : LevGrp La p n → O) (w : Module.Dual O L) (hf : X.IsDer M n f w) :
    X.IsDer M n (fun t => f (levMap p n φ t)) (w ∘ₗ dφ) := by
  obtain ⟨a, ha, hpt⟩ := exists_endo X u φ hu n
  obtain ⟨s, hs, hw⟩ := hf
  refine ⟨(a.left.app ⊤).hom s, fun t => ?_, fun e => ?_⟩
  · rw [valAt_comp, ← Over.comp_left, hpt, hs]
  · obtain ⟨v, hv1, hv2, -⟩ := hw e
    obtain ⟨v', h1, h2, h3⟩ := hw (dφ e)
    refine ⟨v, hv1, hv2, ?_⟩
    have : v ≫ a.left = v' := by
      refine left_ext _ (X.tors n) _ _ ?_ ?_
      · rw [Category.assoc, Over.w, h1, hv1]
      · rw [Category.assoc, ha, h2, hd e, ← Category.assoc, hv2, Over.comp_left, Category.assoc]
    rw [valAt_comp, this, h3]
    simp only [map_one, LinearMap.comp_apply]

set_option linter.unusedVariables false in
theorem tw_funct : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (L : Type) [AddCommGroup L] [Module O L] (M : LieModel G y L), (∀ n f g w, X.IsDer M (n + 1) f w → (∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) → X.IsDer M n g w) ∧ ∀ (u : G ⟶ G) [IsMonHom u] (φ : La →+ La) (dφ : L →ₗ[O] L), X.Induces u φ → M.IsDiffOf u dφ → ∀ n (f g : LevGrp La p n → O), (∀ a, g (lev p n a) = f (lev p n (φ a))) → (f ∈ (X.Γ n).btOrder ⊤ → g ∈ (X.Γ n).btOrder ⊤) ∧ ∀ w, X.IsDer M n f w → X.IsDer M n g (w ∘ₗ dφ) := by
  intro p hpp C _ _ _ v O _ _ _ _ _ _ S _ G _ _ _ y La _ _ _ X L _ _ M
  refine ⟨isDer_res X M, fun u _ φ dφ hu hd n f g hg => ?_⟩
  obtain rfl : g = fun t => f (levMap p n φ t) := by
    funext t
    obtain ⟨b, rfl⟩ := lev_surj p n t
    rw [hg, levMap_lev]
  refine ⟨fun hf => ?_, isDer_endo X M u φ dφ hu hd n f⟩
  obtain ⟨a, -, hpt⟩ := exists_endo X u φ hu n
  have : Finite (LevGrp La p n) := finite_lev hpp.out.ne_zero n
  exact Funct.comp_mem_btOrder O _ _ _ _ a _ hpt f hf

end PositivityTheory.HtPt.Twfunct
end
end

