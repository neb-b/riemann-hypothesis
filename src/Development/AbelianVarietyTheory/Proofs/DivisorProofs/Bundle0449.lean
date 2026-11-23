module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0444
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0013
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0363

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIsGaloisTwistedNormGLMulCardGL
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.NormFibre

theorem card_conj_mul_card_commute {G : Type} [Group G] (g : G) :
    Nat.card {g' : G // IsConj g g'} * Nat.card {x : G // Commute x g} = Nat.card G := by
  have e1 : {g' : G // IsConj g g'} ≃ MulAction.orbit (ConjAct G) g :=
    Equiv.subtypeEquivRight (fun g' => by rw [ConjAct.mem_orbit_conjAct, isConj_comm])
  have e2 : {x : G // Commute x g} ≃ MulAction.stabilizer (ConjAct G) g :=
    { toFun := fun x => ⟨ConjAct.toConjAct x.1, by
          rw [MulAction.mem_stabilizer_iff, ConjAct.toConjAct_smul, x.2.eq, mul_inv_cancel_right]⟩
      invFun := fun y => ⟨ConjAct.ofConjAct y.1, by
          have h := y.2
          rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def, mul_inv_eq_iff_eq_mul] at h
          exact h⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [Nat.card_congr e1, Nat.card_congr e2, ← Nat.card_prod,
    Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct G) g),
    Nat.card_congr (ConjAct.toConjAct (G := G)).toEquiv.symm]

section Fields

variable {F F' : Type} [Field F] [Field F'] [Algebra F F']

theorem galAct_incl (n : ℕ) (t : F' ≃ₐ[F] F') (γ : GL (Fin n) F) :
    galAct F F' n t (incl F F' n γ) = incl F F' n γ := by
  ext i j
  simp [galAct_apply, gal, incl]

theorem galAct_coe (n : ℕ) (t : F' ≃ₐ[F] F') (x : GL (Fin n) F') :
    ((galAct F F' n t x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      (x : Matrix (Fin n) (Fin n) F').map t := by
  ext i j
  simp [galAct_apply, gal]

end Fields

section Count

variable {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']

def nrmFibreEquivOf (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) {n : ℕ}
    {c g' : GL (Fin n) F'} (y : GL (Fin n) F') (hy : y * c * y⁻¹ = g') :
    {δ : GL (Fin n) F' // nrm s δ = g'} ≃ {δ : GL (Fin n) F' // nrm s δ = c} :=
  have htw := (GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n).2.2.1
  { toFun := fun δ => ⟨y⁻¹ * δ.1 * galAct F F' n s y, by
        rw [htw, δ.2, ← hy]; group⟩
    invFun := fun ε => ⟨y * ε.1 * galAct F F' n s y⁻¹, by
        have := htw ε.1 y⁻¹
        rw [inv_inv] at this
        rw [this, ε.2, hy]⟩
    left_inv := fun δ => by
      apply Subtype.ext
      simp only [map_inv]
      group
    right_inv := fun ε => by
      apply Subtype.ext
      simp only [map_inv]
      group }

def nrmFibreEquiv (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) {n : ℕ}
    {c g' : GL (Fin n) F'} (h : IsConj c g') :
    {δ : GL (Fin n) F' // nrm s δ = g'} ≃ {δ : GL (Fin n) F' // nrm s δ = c} :=
  nrmFibreEquivOf s hs _ (isConj_iff.1 h).choose_spec

theorem card_isConj_nrm (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) {n : ℕ}
    (c : GL (Fin n) F') :
    Nat.card {δ : GL (Fin n) F' // IsConj c (nrm s δ)} =
      Nat.card {g' : GL (Fin n) F' // IsConj c g'} * Nat.card {δ : GL (Fin n) F' // nrm s δ = c} := by
  have e : {δ : GL (Fin n) F' // IsConj c (nrm s δ)} ≃
      Σ g' : {g' : GL (Fin n) F' // IsConj c g'}, {δ : GL (Fin n) F' // nrm s δ = g'.1} :=
    { toFun := fun δ => ⟨⟨nrm s δ.1, δ.2⟩, ⟨δ.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by rw [p.2.2]; exact p.1.2⟩
      left_inv := fun δ => rfl
      right_inv := fun p => by
        rcases p with ⟨⟨g', hg⟩, ⟨δ, hδ⟩⟩
        dsimp only at hδ
        subst hδ
        rfl }
  rw [← Nat.card_prod]
  exact Nat.card_congr (e.trans ((Equiv.sigmaCongrRight fun g' => nrmFibreEquiv s hs g'.2).trans
    (Equiv.sigmaEquivProd _ _)))

end Count

section Centraliser

variable {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']

theorem card_nrm_eq_mul_card_commute (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s)
    (n : ℕ) (γ : GL (Fin n) F) :
    Nat.card {δ : GL (Fin n) F' // nrm s δ = incl F F' n γ} * Nat.card {x : GL (Fin n) F // Commute x γ} =
      Nat.card {x : GL (Fin n) F' // Commute x (incl F F' n γ)} := by
  obtain ⟨-, hinj, -, hcomm, hmul⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n
  obtain ⟨δ₀, hδ₀B, hδ₀⟩ := GlobalTheory.T.norm_map_surjective_finite_field F F' s hs n γ
  have hcfix : ∀ t : F' ≃ₐ[F] F', galAct F F' n t (incl F F' n γ) = incl F F' n γ := fun t => galAct_incl n t γ
  set c := incl F F' n γ with hc
  set B := Subalgebra.centralizer F' {(c : Matrix (Fin n) (Fin n) F')} with hB
  have memB : ∀ x : GL (Fin n) F', (x : Matrix (Fin n) (Fin n) F') ∈ B ↔ Commute x c := by
    intro x
    rw [hB, Subalgebra.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    rw [Commute, SemiconjBy, Units.ext_iff, Units.val_mul, Units.val_mul]
    exact eq_comm
  have hcs : (c : Matrix (Fin n) (Fin n) F').map s = c := by rw [← galAct_coe, hcfix]
  have hstab : ∀ x ∈ B, x.map s ∈ B := by
    intro x hx
    rw [hB, Subalgebra.mem_centralizer_iff] at hx ⊢
    simp only [Set.mem_singleton_iff, forall_eq] at hx ⊢
    have e1 : ((c : Matrix (Fin n) (Fin n) F') * x).map s = ((c : Matrix (Fin n) (Fin n) F').map s) * x.map s :=
      Matrix.map_mul (f := (s : F' →+* F'))
    have e2 : (x * (c : Matrix (Fin n) (Fin n) F')).map s = x.map s * ((c : Matrix (Fin n) (Fin n) F').map s) :=
      Matrix.map_mul (f := (s : F' →+* F'))
    rw [hcs] at e1 e2
    rw [← e1, ← e2, hx]
  have h90 := GlobalTheory.T.card_twistedNorm_one_mul_card_fixed_units F F' s hs n B hstab
  have hδ₀comm : ∀ e : GL (Fin n) F', Commute e c → Commute δ₀ e := by
    intro e he
    have hle : Algebra.adjoin F' {(c : Matrix (Fin n) (Fin n) F')} ≤
        Subalgebra.centralizer F' {(e : Matrix (Fin n) (Fin n) F')} := by
      apply Algebra.adjoin_le
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz, SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg, ← Units.val_mul, ← Units.val_mul, he.eq]
    have h1 := hle hδ₀B
    rw [Subalgebra.mem_centralizer_iff] at h1
    have h2 := h1 _ rfl
    exact Units.ext (by rw [Units.val_mul, Units.val_mul]; exact h2.symm)
  have hδ₀c : Commute δ₀ c := hδ₀comm c (Commute.refl c)
  have key : ∀ ε : GL (Fin n) F', Commute ε c → nrm s (δ₀ * ε) = c * nrm s ε := by
    intro ε hε
    rw [hmul δ₀ ε ?_, hδ₀]
    intro t u
    have h3 : Commute δ₀ (galAct F F' n (t⁻¹ * u) ε) := by
      apply hδ₀comm
      have := hε.map (galAct F F' n (t⁻¹ * u))
      rwa [hcfix] at this
    have h4 := h3.map (galAct F F' n t)
    have e : galAct F F' n t (galAct F F' n (t⁻¹ * u) ε) = galAct F F' n u ε := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]
    rwa [e] at h4
  have hYcomm : ∀ δ : GL (Fin n) F', nrm s δ = c → Commute δ c := by
    intro δ h
    have := hcomm δ
    rw [h, hcfix] at this
    exact this
  have eY : {δ : GL (Fin n) F' // nrm s δ = c} ≃
      {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1} :=
    { toFun := fun δ => ⟨δ₀⁻¹ * δ.1, (memB _).2 (hδ₀c.inv_left.mul_left (hYcomm _ δ.2)), by
          have := key (δ₀⁻¹ * δ.1) (hδ₀c.inv_left.mul_left (hYcomm _ δ.2))
          rw [mul_inv_cancel_left, δ.2] at this
          simpa using this.symm⟩
      invFun := fun ε => ⟨δ₀ * ε.1, by rw [key _ ((memB _).1 ε.2.1), ε.2.2, mul_one]⟩
      left_inv := fun δ => Subtype.ext (mul_inv_cancel_left _ _)
      right_inv := fun ε => Subtype.ext (inv_mul_cancel_left _ _) }
  have eC' : {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B} ≃ {x : GL (Fin n) F' // Commute x c} :=
    Equiv.subtypeEquivRight memB
  have eC : {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B} ≃
      {x : GL (Fin n) F // Commute x γ} :=
    Equiv.subtypeEquivRight fun x => by
      rw [memB]
      exact ⟨fun h => hinj (by simpa only [map_mul] using h.eq), fun h => h.map _⟩
  rw [Nat.card_congr eY, ← Nat.card_congr eC, ← Nat.card_congr eC']
  exact h90

end Centraliser

theorem card_isNorm_mul_card : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (γ : GL (Fin n) F),
    Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} * Nat.card (GL (Fin n) F) =
      Nat.card {γ' : GL (Fin n) F // IsConj γ γ'} * Nat.card (GL (Fin n) F') := by
  intro F F' _ _ _ _ s hs n γ
  have hX : Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} =
      Nat.card {g' : GL (Fin n) F' // IsConj (incl F F' n γ) g'} *
        Nat.card {δ : GL (Fin n) F' // nrm s δ = incl F F' n γ} :=
    card_isConj_nrm s hs (incl F F' n γ)
  have hY := card_nrm_eq_mul_card_commute s hs n γ
  have h1 := card_conj_mul_card_commute (incl F F' n γ)
  have h2 := card_conj_mul_card_commute γ
  rw [hX, ← h2, ← h1, ← hY]
  ring

end GlobalTheory.Shin.NormFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductEqZeroOfVanishingOnCover
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem cup_supp_chainsMap_mono (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) [Mono f] (p : ℤ) :
    Mono (((chains R).map f).f p) := by
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨(-p).toNat, by omega⟩
    have hnat := ((GlobalTheory.EtC.chains_basic R).2.1 f N)
    have hm : Mono ((free R).map (f.app (op (SimplexCategory.mk N)))) :=
      ((GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso R (f.app (op (SimplexCategory.mk N)))).1 inferInstance)
    have : ((chains R).map f).f (-(N : ℤ)) =
        ((chains R).map f).f (-(N : ℤ)) ≫ (chainsXIso R E N).hom ≫ (chainsXIso R E N).inv := by simp
    rw [this, ← Category.assoc, hnat, Category.assoc]
    infer_instance
  · haveI := (GlobalTheory.EtC.chains_basic R).1 U
    exact IsZero.mono (isZero_of_isStrictlyLE _ 0 p hp) _

theorem cup_supp_extend (R : Type) [CommRing R] {I : Cx R} (hI : ∀ s, Injective (I.X s)) {U E : Spc} (f : U ⟶ E) [Mono f]
    {n : ℤ} (β : Cochain ((chains R).obj U) I n) :
    ∃ β' : Cochain ((chains R).obj E) I n, (Cochain.ofHom ((chains R).map f)).comp β' (zero_add n) = β := by
  refine ⟨Cochain.mk fun p q h => by
    haveI := cup_supp_chainsMap_mono R f p
    haveI := hI q
    exact Injective.factorThru (β.v p q h) (((chains R).map f).f p), ?_⟩
  refine Cochain.ext _ _ fun p q h => ?_
  haveI := cup_supp_chainsMap_mono R f p
  haveI := hI q
  rw [Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) h, Cochain.ofHom_v, Cochain.mk_v]
  exact Injective.comp_factorThru (J := I.X q) (β.v p q h) (((chains R).map f).f p)

theorem cup_supp_vanish (R : Type) [CommRing R] {K : Cx R} {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (hc : Cover2 R f g)
    {k : ℤ} (γ : Cochain ((chains R).obj E) K k)
    (hf : (Cochain.ofHom ((chains R).map f)).comp γ (zero_add k) = 0)
    (hg : (Cochain.ofHom ((chains R).map g)).comp γ (zero_add k) = 0) : γ = 0 := by
  refine Cochain.ext _ _ fun p q h => ?_
  rw [Cochain.zero_v]
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨(-p).toNat, by omega⟩
    have hf' := congrArg (fun z => z.v (-(N : ℤ)) q h) hf
    have hg' := congrArg (fun z => z.v (-(N : ℤ)) q h) hg
    simp only [Cochain.comp_v _ _ (zero_add k) (-(N : ℤ)) (-(N : ℤ)) q (add_zero _) h, Cochain.ofHom_v,
      Cochain.zero_v] at hf' hg'
    have nf := (GlobalTheory.EtC.chains_basic R).2.1 f N
    have ng := (GlobalTheory.EtC.chains_basic R).2.1 g N
    haveI := hc.2.2 (op (SimplexCategory.mk N))
    have key : biprod.desc ((free R).map (f.app (op (SimplexCategory.mk N))))
        ((free R).map (g.app (op (SimplexCategory.mk N)))) ≫ ((chainsXIso R E N).inv ≫ γ.v (-(N : ℤ)) q h) = 0 := by
      apply biprod.hom_ext'
      · rw [biprod.inl_desc_assoc, comp_zero]
        have : (free R).map (f.app (op (SimplexCategory.mk N))) =
            (chainsXIso R U N).inv ≫ ((chains R).map f).f (-(N : ℤ)) ≫ (chainsXIso R E N).hom := by
          rw [nf]; simp
        rw [this]; simp [hf']
      · rw [biprod.inr_desc_assoc, comp_zero]
        have : (free R).map (g.app (op (SimplexCategory.mk N))) =
            (chainsXIso R V N).inv ≫ ((chains R).map g).f (-(N : ℤ)) ≫ (chainsXIso R E N).hom := by
          rw [ng]; simp
        rw [this]; simp [hg']
    have h0 : (chainsXIso R E N).inv ≫ γ.v (-(N : ℤ)) q h = 0 := by
      rw [← cancel_epi (biprod.desc ((free R).map (f.app (op (SimplexCategory.mk N))))
        ((free R).map (g.app (op (SimplexCategory.mk N))))), key, comp_zero]
    have : γ.v (-(N : ℤ)) q h = (chainsXIso R E N).hom ≫ ((chainsXIso R E N).inv ≫ γ.v (-(N : ℤ)) q h) := by simp
    rw [this, h0, comp_zero]
  · haveI := (GlobalTheory.EtC.chains_basic R).1 E
    exact (isZero_of_isStrictlyLE _ 0 p hp).eq_of_src _ _

theorem cup_supp_rep (R : Type) [CommRing R] {I : Cx R} (hI : ∀ s, Injective (I.X s)) {U E : Spc} (f : U ⟶ E) [Mono f]
    {n : ℤ} (a : CohomologyClass ((chains R).obj E) I n) (ha : cpull ((chains R).map f) I n a = 0) :
    ∃ α : Cocycle ((chains R).obj E) I n, CohomologyClass.mk α = a ∧
      (Cochain.ofHom ((chains R).map f)).comp α.1 (zero_add n) = 0 := by
  obtain ⟨α, rfl⟩ := a.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) α (zero_add n)) = 0 at ha
  rw [CohomologyClass.mk_eq_zero_iff] at ha
  obtain ⟨n', hn', β, hβ⟩ := ha
  have hβ2 : δ n' n β = (Cochain.ofHom ((chains R).map f)).comp α.1 (zero_add n) := hβ
  obtain ⟨β', hβ'⟩ := cup_supp_extend R hI f β
  let c : Cocycle ((chains R).obj E) I n := Cocycle.mk (δ n' n β') (n + 1) rfl (δ_δ _ _ _ _)
  refine ⟨α - c, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, sub_eq_self, CohomologyClass.mk_eq_zero_iff]
    exact ⟨n', hn', β', rfl⟩
  · change (Cochain.ofHom ((chains R).map f)).comp (α.1 - δ n' n β') (zero_add n) = 0
    rw [Cochain.comp_sub, ← δ_ofHom_comp, hβ', hβ2, sub_self]

theorem cup_supp (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (hI : ∀ s, Injective (I.X s))
    (hJ : ∀ s, Injective (J.X s)) {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (hc : Cover2 R f g) {n m k : ℤ}
    (hk : n + m = k) (a : CohomologyClass ((chains R).obj E) I n) (b : CohomologyClass ((chains R).obj E) J m)
    (ha : cpull ((chains R).map f) I n a = 0) (hb : cpull ((chains R).map g) J m b = 0) : μ.cup E hk a b = 0 := by
  haveI := hc.1
  haveI := hc.2.1
  obtain ⟨α, rfl, hα⟩ := cup_supp_rep R hI f a ha
  obtain ⟨β, rfl, hβ⟩ := cup_supp_rep R hJ g b hb
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ hk).1 α β
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R μ hk).2 α β γ hγ, CohomologyClass.mk_eq_zero_iff]
  have evK := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := K) (n := k)
  have evI := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := I) (n := n)
  have evJ := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := J) (n := m)
  have h1 : (Cochain.ofHom ((chains R).map f)).comp γ.1 (zero_add k) = 0 := by
    have evKU := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := U) (I := K) (n := k)
    have evIU := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := U) (I := I) (n := n)
    apply evKU.2.2.1
    intro N w h U' x
    rw [evK.2.2.2.1 f γ.1 N w h U' x, (evKU.1 0 0 N w h U' x).2.2.1, hγ N w h U' (x.map f)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [((GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite x).2.2.1 0 i (by omega)).2.1 f,
      ← evI.2.2.2.1 f α.1, hα, (evIU.1 0 0 _ _ rfl U' (x.sub 0 i (by omega))).2.2.1]
    simp
  have h2 : (Cochain.ofHom ((chains R).map g)).comp γ.1 (zero_add k) = 0 := by
    have evKV := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := V) (I := K) (n := k)
    have evJV := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := V) (I := J) (n := m)
    apply evKV.2.2.1
    intro N w h U' x
    rw [evK.2.2.2.1 g γ.1 N w h U' x, (evKV.1 0 0 N w h U' x).2.2.1, hγ N w h U' (x.map g)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [((GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite x).2.2.1 i (N - i) (by omega)).2.1 g,
      ← evJ.2.2.2.1 g β.1, hβ, (evJV.1 0 0 _ _ rfl U' (x.sub i (N - i) (by omega))).2.2.1]
    simp
  have h0 : γ = 0 := Cocycle.ext (cup_supp_vanish R f g hc γ.1 h1 h2)
  rw [h0]
  exact zero_mem _

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormPullbackIsBoundedSectionStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_pullback_isBoundedSection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → ∀ (h : U) (c : C), (M.comp c).IsBddSec (castWt (M.comp_Ψ c) la) (fun x => M.pull h F c (castFrame (M.comp_Ψ c) x)) := by
  first | exact @GlobalTheory.PullBdd.pull_isBddSec | exact GlobalTheory.PullBdd.pull_isBddSec | (intros; apply GlobalTheory.PullBdd.pull_isBddSec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTermOrigin
section
noncomputable section

open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates

namespace GlobalTheory.DeformedSum

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def dTerm (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (z : I → ℂ) (x : E) : ℂ :=
  ∏ i, (((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)) * (starRingEnd ℂ (φ i x)) ^ m i *
    (defCoord φ z x i)⁻¹ ^ (k + m i))

theorem dTerm_zero (φ : I → E →+* ℂ) (k : ℕ) (z : I → ℂ) (x : E) :
    dTerm φ k 0 z x = ∏ i, (defCoord φ z x i)⁻¹ ^ k := by
  simp [dTerm]

theorem dTerm_origin (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (x : E) :
    dTerm φ k m 0 x = risingFactor k m * ∏ i, ((φ i x)⁻¹ ^ (k + m i) * (starRingEnd ℂ (φ i x)) ^ m i) := by
  unfold dTerm risingFactor
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [defCoord, Pi.zero_apply, zero_mul, add_zero]
  ring

end GlobalTheory.DeformedSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassProperties
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SectionClass

variable (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})

theorem exists_cocycle (s : Sec F X) :
    ∃ α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0, ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s := by
  have hz : Sec.map ((res R F).d 0 1) (Sec.map (resι R F) s) = 0 :=
    ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).1 _).2 ⟨s, rfl⟩
  obtain ⟨α, h0, -⟩ := (GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (-1) 0 1 (by norm_num) (by norm_num)).1 _ hz
  refine ⟨α, (h0 X (𝟙 X)).trans ?_⟩
  simp [Sec.res]

theorem mk_eq_iff (α β : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0) :
    CohomologyClass.mk α = CohomologyClass.mk β ↔
      ev α.1 0 0 (by simp) X (𝟙 X) = ev β.1 0 0 (by simp) X (𝟙 X) := by
  have h2 := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (-1) 0 1 (by norm_num) (by norm_num)).2 (α - β)).2
  have hsub : ev (α - β).1 0 0 (by simp) X (𝟙 X) = ev α.1 0 0 (by simp) X (𝟙 X) - ev β.1 0 0 (by simp) X (𝟙 X) := by
    have := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).1 α.1 β.1 0 0 (by simp) X (𝟙 X)).2.1
    simpa using this
  have hss : Subsingleton (Sec ((res R F).X (-1)) X) := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).2.2.2 (-1) (by norm_num)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, h2, hsub]
  have hz : Sec.map ((res R F).d (-1) 0) (0 : Sec ((res R F).X (-1)) X) = 0 := map_zero _
  constructor
  · rintro ⟨y, hy⟩
    have hy' : (0 : Sec ((res R F).X 0) X) = ev α.1 0 0 (by simp) X (𝟙 X) - ev β.1 0 0 (by simp) X (𝟙 X) := by
      rw [← hz, ← Subsingleton.elim y 0]; exact hy
    exact (sub_eq_zero.1 hy'.symm)
  · intro h
    refine ⟨0, ?_⟩
    rw [hz, h, sub_self]

theorem secClass_spec (s : Sec F X) : ∃ α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0,
    CohomologyClass.mk α = secClass F s ∧ ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s := by
  obtain ⟨α, h⟩ := exists_cocycle R F X s
  exact pick_spec (P := fun c => ∃ α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0,
    CohomologyClass.mk α = c ∧ ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s) ⟨_, α, rfl, h⟩

theorem spec_iff (s : Sec F X) (α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0) :
    ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s ↔ CohomologyClass.mk α = secClass F s := by
  obtain ⟨α₀, h1, h2⟩ := secClass_spec R F X s
  rw [← h1, mk_eq_iff, h2]

end GlobalTheory.EtC.SectionClass


open GlobalTheory.EtC.SectionClass in
theorem GlobalTheory.EtC.secClass_props : ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}), (∀ (s : Sec F X) (α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0), ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s ↔ CohomologyClass.mk α = secClass F s) ∧ Function.Bijective (secClass F (X := X)) ∧ (∀ s t : Sec F X, secClass F (s + t) = secClass F s + secClass F t) ∧ (∀ {Y : Scheme.{0}} (f : Y ⟶ X) (s : Sec F X), pull R (sch.map f) F 0 (secClass F s) = secClass F (Sec.res f s)) ∧ ∀ {G : Shv R} (φ : F ⟶ G) (s : Sec F X), HK.post R _ φ 0 (secClass F s) = secClass G (Sec.map φ s) := by
  intro R _ F X
  refine ⟨spec_iff R F X, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro s t hst
    obtain ⟨α, h1, h2⟩ := secClass_spec R F X s
    have h3 := (spec_iff R F X t α).2 (h1.trans hst)
    exact (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).2.1 (h2.symm.trans h3)
  · intro c
    obtain ⟨α, rfl⟩ := c.mk_surjective
    have hd := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (-1) 0 1 (by norm_num) (by norm_num)).2 α).1
    obtain ⟨a, ha⟩ := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).1 _).1 hd
    exact ⟨a, ((spec_iff R F X a α).1 ha.symm).symm⟩
  · intro s t
    obtain ⟨α, h1, h2⟩ := secClass_spec R F X s
    obtain ⟨β, h3, h4⟩ := secClass_spec R F X t
    rw [← h1, ← h3, ← CohomologyClass.mk_add]
    symm
    refine (spec_iff R F X (s + t) (α + β)).1 ?_
    have := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).1 α.1 β.1 0 0 (by simp) X (𝟙 X)).1
    simp only [Cocycle.coe_add] at this ⊢
    rw [this, h2, h4]
    exact (map_add ((resι R F).hom.app (op X)).hom s t).symm
  · intro Y f s
    obtain ⟨α, h1, h2⟩ := secClass_spec R F X s
    rw [← h1]
    refine (spec_iff R F Y _ _).1 ?_
    have e4 := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).2.2.2.1 (sch.map f) α.1 0 0 (by simp) Y (𝟙 Y)
    have e2 := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).2.1 α.1 0 0 (by simp) Y X f (𝟙 X)
    have hx1 : Sx.map (p := 0) (sch.map f) (𝟙 Y : Sx (sch.obj Y) 0 Y) = (show Sx (sch.obj X) 0 Y from f) := by
      simp [Sx.map, sch]
      exact Category.id_comp f
    have hx2 : Sx.res f (𝟙 X : Sx (sch.obj X) 0 X) = (show Sx (sch.obj X) 0 Y from f) := by
      simp [Sx.res, sch]
      exact Category.comp_id f
    change ev ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add 0)) 0 0 _ Y (𝟙 Y) = _
    rw [e4, hx1, ← hx2, ← e2, h2]
    exact (NatTrans.naturality_apply (resι R F).hom f.op s).symm
  · intro G φ s
    obtain ⟨α, h1, h2⟩ := secClass_spec R F X s
    rw [← h1]
    refine (spec_iff R G X _ _).1 ?_
    have e5 := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).2.2.2.2 (resMap R φ) α.1 0 0 (by simp) X (𝟙 X)
    have hc := ((_root_.GlobalTheory.EtC.ResBasic.res_basic R F).2.2.2.2.2.2.2 G φ).2
    change ev (α.1.comp (Cochain.ofHom (resMap R φ)) (add_zero 0)) 0 0 _ X (𝟙 X) = _
    rw [e5, h2]
    change ((resι R F ≫ (resMap R φ).f 0).hom.app (op X)).hom s = _
    rw [hc]
    rfl
end

