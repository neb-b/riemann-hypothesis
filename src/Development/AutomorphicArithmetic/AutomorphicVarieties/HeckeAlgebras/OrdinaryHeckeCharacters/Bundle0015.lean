module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0061
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0056
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2LocSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.HeckePolCoeff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0013

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2ActEx
section
section Helpers
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem ae_abs {A R P Lev B ι : Type} [CommRing A] [CommRing R] [AddCommGroup P] [Module A P] [Nonempty Lev] [Group B]
    (MK : Lev → Submodule A P) (S : Submodule A P) (op : ι → Module.End A P) (ρ : Representation A B S) (κ : Lev → Subgroup B)
    (hfix : ∀ K, (fixd ρ (κ K)).map S.subtype = MK K) (hex : ∀ f : S, ∃ K, (f : P) ∈ MK K)
    (hinf : ∀ K K', ∃ K'', κ K'' ≤ κ K ∧ κ K'' ≤ κ K') (hconj : ∀ K g, ∃ K', ∀ k ∈ κ K', g⁻¹ * k * g ∈ κ K)
    (hop : ∀ g i (z z' : S), (z' : P) = op i z → (ρ g z' : P) = op i (ρ g z))
    (μ : ∀ K, R →+* Module.End A (MK K))
    (hμ : ∀ K K' (φ : MK K →ₗ[A] MK K'), Function.Injective φ →
      (∀ i (y y' : MK K), (y' : P) = op i y → (φ y' : P) = op i (φ y)) → ∀ t y, φ (μ K t y) = μ K' t (φ y)) :
    ∃ α : R →+* Module.End A S, (∀ t g z, α t (ρ g z) = ρ g (α t z)) ∧
      ∀ K t (y : MK K) (z : S), (z : P) = y → (α t z : P) = μ K t y := by
  have hle : ∀ K, MK K ≤ S := fun K => by
    rw [← hfix]
    exact Submodule.map_subtype_le _ _
  have hmem : ∀ K (z : S), (z : P) ∈ MK K ↔ z ∈ fixd ρ (κ K) := fun K z => by
    rw [← hfix]
    exact ⟨fun ⟨y, hy, e⟩ => Subtype.ext e ▸ hy, fun h => ⟨z, h, rfl⟩⟩
  let e : ∀ K, (MK K).comap S.subtype ≃ₗ[A] MK K := fun K => Submodule.comapSubtypeEquivOfLe (hle K)
  have he : ∀ K y, (e K y : P) = (y : S) := fun _ _ => rfl
  have he' : ∀ K y, (((e K).symm y : S) : P) = y := fun K y => by rw [← he, LinearEquiv.apply_symm_apply]
  obtain ⟨α, hα⟩ := levelUR2Glue A R S Lev (fun K => (MK K).comap S.subtype)
    (fun K => (e K).symm.conjRingEquiv.toRingHom.comp (μ K)) hex
    (fun K K' => by
      obtain ⟨K'', h1, h2⟩ := hinf K K'
      exact ⟨K'', fun z hz => (hmem _ z).2 fun k hk => (hmem _ z).1 hz k (h1 hk),
        fun z hz => (hmem _ z).2 fun k hk => (hmem _ z).1 hz k (h2 hk)⟩)
    (fun K K' h t y => by
      have h' : MK K ≤ MK K' := fun x hx => h (x := ⟨x, hle K hx⟩) hx
      have := hμ K K' (Submodule.inclusion h') (Submodule.inclusion_injective h') (fun i y y' hy => hy) t (e K y)
      refine Subtype.ext ?_
      exact (he' K' _).trans ((congrArg Subtype.val this).symm.trans (he' K _).symm))
  have h2 : ∀ K t (y : MK K) (z : S), (z : P) = y → (α t z : P) = μ K t y := fun K t y z hz => by
    have hy : y = e K ⟨z, show (z : P) ∈ MK K from hz ▸ y.2⟩ := Subtype.ext hz.symm
    rw [hy]
    exact (congrArg Subtype.val (hα K t ⟨z, show (z : P) ∈ MK K from hz ▸ y.2⟩)).trans (he' K _)
  refine ⟨α, fun t g z => ?_, h2⟩
  obtain ⟨K, hK⟩ := hex z
  obtain ⟨K', hK'⟩ := hconj K g
  let φ : MK K →ₗ[A] MK K' := (S.subtype ∘ₗ ρ g ∘ₗ Submodule.inclusion (hle K)).codRestrict _ fun y =>
    (hmem K' _).2 fun k hk => by
      have := (hmem K (Submodule.inclusion (hle K) y)).1 y.2 _ (hK' k hk)
      change ρ k (ρ g _) = ρ g _
      conv_rhs => rw [← this]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel_left]
  have hφ : ∀ y, (φ y : P) = ρ g (Submodule.inclusion (hle K) y) := fun _ => rfl
  have hinj : Function.Injective φ := fun y y' h => by
    have h3 : ρ g (Submodule.inclusion (hle K) y) = ρ g (Submodule.inclusion (hle K) y') :=
      Subtype.ext (by rw [← hφ, ← hφ, h])
    have h4 := congrArg (ρ g⁻¹) h3
    simp only [Representation.inv_self_apply] at h4
    exact Submodule.inclusion_injective _ h4
  have h5 := hμ K K' φ hinj (fun i y y' hy => hop g i _ _ hy) t ⟨z, hK⟩
  refine Subtype.ext ?_
  rw [h2 K' t (φ ⟨z, hK⟩) (ρ g z) rfl, ← h5, hφ]
  exact congrArg (fun x => (ρ g x : P)) (Subtype.ext (h2 K t ⟨z, hK⟩ z rfl).symm)

private theorem ae_ind {Q : Type} [Fintype Q] [DecidableEq Q] {G : Q → Type} [∀ q, Group (G q)] (p : (∀ q, G q) → Prop)
    (h1 : p 1) (hm : ∀ g g', p g → p g' → p (g * g')) (hs : ∀ q g, p (Pi.mulSingle q g)) (g : ∀ q, G q) : p g := by
  rw [← Finset.noncommProd_mulSingle g]
  exact Finset.noncommProd_induction _ _ _ p hm h1 fun q _ => hs q _

private theorem ae_gen {Q : Type} [Fintype Q] [DecidableEq Q] {G : Q → Type} [∀ q, Group (G q)] {A P ι : Type} [CommRing A]
    [AddCommGroup P] [Module A P] (S : Submodule A P) (op : ι → Module.End A P) (ρ : Representation A (∀ q, G q) S)
    (s : ∀ q, G q → Module.End A P) (hρ : ∀ q g f, (ρ (Pi.mulSingle q g) f : P) = s q g f)
    (hop : ∀ q g i, Commute (s q g) (op i)) :
    ∀ g i (z z' : S), (z' : P) = op i z → (ρ g z' : P) = op i (ρ g z) :=
  ae_ind _ (fun i z z' h => by simpa using h)
    (fun g g' hg hg' i z z' h => by
      rw [map_mul]
      exact hg i _ _ (hg' i z z' h))
    (fun q g i z z' h => by rw [hρ, hρ, h, ← Module.End.mul_apply, (hop q g i).eq, Module.End.mul_apply])

section Top

variable {Q : Type} {G : Q → Type} [∀ q, Group (G q)] [∀ q, TopologicalSpace (G q)] [∀ q, IsTopologicalGroup (G q)]

private theorem ae_inf (K K' : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))}) :
    ∃ K'' : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))},
      Subgroup.pi Set.univ K''.1 ≤ Subgroup.pi Set.univ K.1 ∧ Subgroup.pi Set.univ K''.1 ≤ Subgroup.pi Set.univ K'.1 :=
  ⟨⟨fun q => K.1 q ⊓ K'.1 q, fun q => ⟨(K.2 q).1.inter (K'.2 q).1,
      (K.2 q).2.inter_right ((K'.1 q).isClosed_of_isOpen (K'.2 q).1)⟩⟩,
    fun _ hk q hq => (hk q hq).1, fun _ hk q hq => (hk q hq).2⟩

private theorem ae_conj (K : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))})
    (g : ∀ q, G q) : ∃ K' : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))},
      ∀ k ∈ Subgroup.pi Set.univ K'.1, g⁻¹ * k * g ∈ Subgroup.pi Set.univ K.1 :=
  ⟨⟨fun q => (K.1 q).comap (MulAut.conj (g q)⁻¹).toMonoidHom, fun q => by
      let e := (Homeomorph.mulLeft (g q)⁻¹).trans (Homeomorph.mulRight (g q)⁻¹⁻¹)
      exact ⟨(K.2 q).1.preimage e.continuous, e.isCompact_preimage.2 (K.2 q).2⟩⟩,
    fun k hk q hq => by simpa using hk q hq⟩

end Top

private theorem ae_commU {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A] {m : ℕ}
    (τ : X.Ub →* GL (Fin m) A) (u : X.Ub) (b : Gp) : Commute (X.ra τ u) (X.U A m b) := by
  unfold Frame.U Iwa.uOp
  refine finsum_induction (fun t => Commute (X.ra τ u) t) (Commute.zero_right _) (fun _ _ => Commute.add_right) fun q => ?_
  refine LinearMap.ext fun f => funext fun g => ?_
  change (τ u : Matrix (Fin m) (Fin m) A) *ᵥ f (g * ((u : Ga), 1) * (1, _)) =
    (τ u : Matrix (Fin m) (Fin m) A) *ᵥ f (g * (1, _) * ((u : Ga), 1))
  simp [mul_assoc]

private theorem ae_dc {A H H' M : Type} [CommRing A] [Group H] [Group H'] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (s : H' →* H) (u : H) (h : ∀ g, Commute u (s g)) (K K' : Subgroup H') (x : H') :
    Commute (ρ u) (dc (ρ.comp s) K K' x) :=
  finsum_induction (fun t => Commute (ρ u) t) (Commute.zero_right _) (fun _ _ => Commute.add_right) fun _ => (h _).map ρ

private theorem ae_bot {A R P : Type} [CommRing A] [CommRing R] [AddCommGroup P] [Module A P] {Y : Submodule A P} (h : Y = ⊥)
    (lam : A → R) : ∃ μ : R →+* Module.End A Y, (∀ b y, μ (lam b) y = b • y) ∧ Subsingleton Y := by
  haveI : Subsingleton Y := h ▸ inferInstance
  exact ⟨⟨⟨⟨fun _ => 0, Subsingleton.elim _ _⟩, fun _ _ => Subsingleton.elim _ _⟩, rfl, fun _ _ => Subsingleton.elim _ _⟩,
    fun _ _ => Subsingleton.elim _ _, this⟩

private theorem ae_mu {O A R P ι : Type} [CommRing O] [CommRing A] [CommRing R] [AddCommGroup P] [Module A P]
    {Y : Submodule A P} {op : ι → Module.End A P} [Fact (CommOn Y op)] [Algebra O R] [Algebra O (heckeAlg Y op)]
    (f : R →ₐ[O] heckeAlg Y op) (lam : A → R) (hl : ∀ b, f (lam b) = algebraMap A _ b) :
    ∃ μ : R →+* Module.End A Y, (∀ t, μ t = (f t : Module.End A Y)) ∧ ∀ b y, μ (lam b) y = b • y := by
  refine ⟨(heckeAlg Y op).val.toRingHom.comp f.toRingHom, fun _ => rfl, fun b y => ?_⟩
  change (f (lam b) : Module.End A Y) y = _
  rw [hl]
  rfl

private theorem ae_nt {A P ι : Type} [CommRing A] [AddCommGroup P] [Module A P] {Y : Submodule A P}
    {op : ι → Module.End A P} [Nontrivial (heckeAlg Y op)] : ¬ Subsingleton Y := fun _ =>
  absurd (inferInstance : Subsingleton (heckeAlg Y op)) (not_subsingleton _)

private theorem ae_zero {A M N : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (h : Subsingleton M) (φ : M →ₗ[A] N) (s : Module.End A M) (t : Module.End A N) (y : M) : φ (s y) = t (φ y) := by
  rw [Subsingleton.elim y 0, map_zero, map_zero, map_zero]

end Helpers

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ)
  (a : H.Op → c.O) {R : Type} [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq)
  (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ)

private def ae_Ok (K : H.Lev) (μ : R →+* Module.End A (H.MK θ a K)) : Prop :=
  Subsingleton (H.MK θ a K) ∨
    ∃ (_ : Fact (CommOn (H.MK θ a K) (H.op A))) (_ : Alg.IsCO c.O (H.TK θ a K)) (f : R →ₐ[c.O] H.TK θ a K),
      H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A (H.MK θ a K))

private theorem ae_ex (lam : A →ₐ[c.O] R) (K : H.Lev) (J : Ideal R) (hJ : H.IsJ θ a K D₀ ψ₀ lam J) :
    ∃ μ : R →+* Module.End A (H.MK θ a K), (∀ b y, μ (lam b) y = b • y) ∧ ae_Ok H θ a D₀ ψ₀ K μ := by
  rcases hJ with h | ⟨i1, i2, f, -, hf, -, hl, -⟩
  · exact (ae_bot (A := A) (R := R) (P := H.X.Fn A H.m) (Y := H.MK θ a K) h.1 lam).imp fun μ h => ⟨h.1, .inl h.2⟩
  · exact (ae_mu (A := A) (P := H.X.Fn A H.m) (Y := H.MK θ a K) (op := H.op A) f lam hl).imp
      fun μ h => ⟨h.2, .inr ⟨i1, i2, f, hf, h.1⟩⟩

private theorem ae_cmp (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) (hH : H.Ax) (hθ : H.IsWt θ)
    (hU : ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T),
      D₀.map f.toRingHom = D₀.map g.toRingHom →
      (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = W.pushCh g.toRingHom (ψ₀ v i)) → f = g)
    (K K' : H.Lev) (μ : R →+* Module.End A (H.MK θ a K)) (μ' : R →+* Module.End A (H.MK θ a K'))
    (h : ae_Ok H θ a D₀ ψ₀ K μ) (h' : ae_Ok H θ a D₀ ψ₀ K' μ') (φ : H.MK θ a K →ₗ[A] H.MK θ a K') (hφ : Function.Injective φ)
    (hc : ∀ i (y y' : H.MK θ a K), (y' : H.X.Fn A H.m) = H.op A i y → (φ y' : H.X.Fn A H.m) = H.op A i (φ y)) (t : R)
    (y : H.MK θ a K) : φ (μ t y) = μ' t (φ y) := by
  rcases h with h | ⟨i1, i2, f, hf, e⟩
  · exact ae_zero h φ (μ t) (μ' t) y
  rcases h' with h | ⟨i1', i2', f', hf', e'⟩
  · exact h.elim _ _
  rw [e, e']
  exact levelUR2Compat hN L Ω l n c H hH A θ hθ a K K' R D₀ ψ₀ hU f f' hf hf' φ hφ (fun i y => hc i y _ rfl) t y

private theorem ae_out (K : H.Lev) (μ : R →+* Module.End A (H.MK θ a K)) (h : ae_Ok H θ a D₀ ψ₀ K μ)
    [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)] :
    ∃ f : R →ₐ[c.O] H.TK θ a K, H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A (H.MK θ a K)) := by
  rcases h with h | ⟨_, _, h⟩
  · exact absurd h (ae_nt (op := H.op A))
  · exact h

private theorem ae_op (hH : H.Ax) (q : H.Q) (g : GLw n (H.wq q)) (i : H.Op) :
    Commute (H.X.ra (H.τA A) (H.sec (H.wq q) g)) (H.op A i) := by
  rcases i with x | x
  · exact ae_dc _ _ _ (hH.sectionsCommuteAtSplit q _ x.1.2 g) _ _ _
  · exact ae_commU _ _ _ _

end

theorem UpperTheory.V.Hi.levelUR2ActEx :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) [DecidableEq H.Q] (ρ : Representation A (GV n H.wq) (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (∀ q g f, (ρ (Pi.mulSingle q g) f : H.X.Fn A H.m) = H.X.ra (H.τA A) (H.sec (H.wq q) g) f) → (∀ K : H.Lev, (fixd ρ (Subgroup.pi Set.univ K.1)).map (Submodule.subtype _) = H.MK θ a K) → (∀ f : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)), ∃ K, (f : H.X.Fn A H.m) ∈ H.MK θ a K) → ∀ (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ) (lam : A →ₐ[c.O] R), (∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T), D₀.map f.toRingHom = D₀.map g.toRingHom → (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = W.pushCh g.toRingHom (ψ₀ v i)) → f = g) → (∀ K, ∃ J, H.IsJ θ a K D₀ ψ₀ lam J) → ∃ α : R →+* Module.End A (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)), (∀ b z, α (lam b) z = b • z) ∧ (∀ t g z, α t (ρ g z) = ρ g (α t z)) ∧ ∀ (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∃ f : R →ₐ[c.O] H.TK θ a K, H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t (y : H.MK θ a K) (z : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (z : H.X.Fn A H.m) = y → (α t z : H.X.Fn A H.m) = ((f t : Module.End A (H.MK θ a K)) y : H.MK θ a K) := by
  intro hN L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ a _ ρ hρ hfix hex R _ _ D₀ ψ₀ lam hU hJ
  haveI : Nonempty H.Lev := ⟨⟨fun q => KO _ (Fin n), fun q => ⟨GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isCompact_KO⟩⟩⟩
  choose μ hμ1 hμ2 using fun K => ae_ex H θ a D₀ ψ₀ lam K _ (hJ K).choose_spec
  obtain ⟨α, h1, h2⟩ := ae_abs (H.MK θ a) _ (H.op A) ρ (fun K : H.Lev => Subgroup.pi Set.univ K.1) hfix hex ae_inf ae_conj
    (ae_gen _ (H.op A) ρ (fun q g => H.X.ra (H.τA A) (H.sec (H.wq q) g)) hρ (ae_op H hH)) μ
    (fun K K' => ae_cmp H θ a D₀ ψ₀ hN hH hθ hU K K' _ _ (hμ2 K) (hμ2 K'))
  refine ⟨α, fun b z => ?_, h1, fun K i1 i2 => ?_⟩
  · obtain ⟨K, hK⟩ := hex z
    exact Subtype.ext ((h2 K _ ⟨z, hK⟩ z rfl).trans (congrArg Subtype.val (hμ1 K b ⟨z, hK⟩)))
  · obtain ⟨f, hf, e⟩ := ae_out H θ a D₀ ψ₀ K _ (hμ2 K)
    refine ⟨f, hf, fun t y z hz => ?_⟩
    rw [← e]
    exact h2 K t y z hz
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2LevEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem le_mem_under {l : ℕ} {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) :
    ((l : ℕ) : 𝓞 L) ∈ w.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal := by
  change _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ w.asIdeal
  rw [map_natCast]

private theorem le_cmp_same {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w w' : Plc L}
    (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) (g : Ga l L n)
    (hg : cmp n w g ∈ KO (w.adicCompletion L) (Fin n)) : cmp n w' g ∈ KO (w'.adicCompletion L) (Fin n) := by
  by_cases h' : ((l : ℕ) : 𝓞 L) ∉ w'.asIdeal
  · have h0 : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := by
      rw [le_mem_under, ← h, ← le_mem_under]
      exact h'
    obtain ⟨_, x, rfl⟩ := g
    unfold CaseU.cmp at hg ⊢
    rw [dite_eq_left h0] at hg
    rw [dite_eq_left h']
    exact UpperTheory.mem_maximalCompact_of_under_eq L n x w w' h hg
  · unfold CaseU.cmp
    rw [dite_eq_right h']
    exact one_mem _

theorem UpperTheory.V.Hi.levelUR2LevEq :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V₀ V : s.Lev) (Q₀ : QData V₀) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (K₀ : (hset Q₀ τ₀).Lev) (K : (hset Q τ₀).Lev), V₀.S' = s.S → (∀ q, K.1 q = KO ((Q.wq q).adicCompletion L) (Fin n)) → ∀ u : Ub n s, u ∈ (hset Q τ₀).lev K ↔ u ∈ (hset Q₀ τ₀).lev K₀ := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V₀ V Q₀ Q c m τ₀ K₀ K h0 hK u
  have hem : ∀ q : Q₀.Q, False := fun q => by
    refine Q₀.notS q ?_
    rw [← h0, Q₀.range]
    exact Or.inr ⟨q, rfl⟩
  constructor
  · intro hu
    obtain ⟨h1, h2⟩ := levelUR2LevOut l L Ω s n hn V Q c m τ₀ K u hu
    refine UpperTheory.mem_heckeLevel_of_local_components_mem l L Ω s n hn V₀ Q₀ c m τ₀ K₀ u (fun w hw => ?_) fun q => (hem q).elim
    by_cases hw' : w.under (𝓞 (Lp L)) ∈ V.S'
    · rw [Q.range] at hw'
      rcases hw' with hw' | ⟨q, hq⟩
      · exact (hw (h0 ▸ hw')).elim
      · refine le_cmp_same (w := Q.wq q) hq.symm _ ?_
        have h3 := h2 q
        rw [hK q] at h3
        exact h3
    · exact h1 w hw'
  · intro hu
    obtain ⟨h1, _⟩ := levelUR2LevOut l L Ω s n hn V₀ Q₀ c m τ₀ K₀ u hu
    refine UpperTheory.mem_heckeLevel_of_local_components_mem l L Ω s n hn V Q c m τ₀ K u (fun w hw => h1 w fun hw' => hw ?_) fun q => ?_
    · rw [Q.range]
      exact Or.inl (h0 ▸ hw')
    · rw [hK q]
      exact h1 _ (h0 ▸ Q.notS q)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ModuleStructureOfCommuting
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance 2000] UpperTheory.V.W.coefLocal
set_option synthInstance.maxHeartbeats 200000

private theorem hecke_poly_coeff_formula {A : Type} [CommRing A] (n q : ℕ) (a : ℕ → A) (j : ℕ) (hj : j ≤ n) :
    (heckePol n q a).coeff (n - j) = (-1) ^ j * (q : A) ^ (j * (j - 1) / 2) * a j := by
  rw [mul_assoc, ← JEx.heckePol_coeff n q a j hj, ← mul_assoc, ← mul_pow]
  simp

private theorem hecke_poly_coeff_zero {A : Type} [CommRing A] (n q : ℕ) (a : ℕ → A) (i : ℕ) (hi : n < i) :
    (heckePol n q a).coeff i = 0 := by
  rw [Hi.heckePol, finsetSum_coeff]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [coeff_C_mul_X_pow, if_neg]
  omega

private theorem norm_lt_one_of_residue_zero {l : ℕ} [Fact l.Prime] (c : Coef l) (b : c.O) (hb : residue c.O b = 0) :
    ‖algebraMap c.O (Qbar l) b‖ < 1 := by
  have e : algebraMap c.O (Qbar l) b = (b : PadicAlgCl l) := rfl
  rw [e]
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at hb
  rcases eq_or_ne b 0 with rfl | h0
  · simp
  have h := UpperTheory.V.Base.normO l c.O b h0
  have hl : ((l : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hv : (IsDiscreteValuationRing.addVal c.O b).toNat ≠ 0 := by
    rw [Ne, ENat.toNat_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact fun h => h.elim hb h0
  have h1 := pow_lt_one₀ (by positivity) hl hv
  rw [← h] at h1
  by_contra hn
  exact absurd h1 (not_lt.2 (one_le_pow₀ (not_lt.1 hn)))

private theorem hecke_poly_coeff_congruence_iff {l : ℕ} [Fact l.Prime] (c : Coef l) (n q : ℕ) (hq : ‖(q : Qbar l)‖ = 1) (a : ℕ → Qbar l) (b : ℕ → c.O) :
    (∀ j ≤ n, ‖a j - algebraMap c.O (Qbar l) (b j)‖ < 1) ↔
      ∀ (i : ℕ) (b' : c.O), residue c.O b' = (heckePol n q fun j => residue c.O (b j)).coeff i →
        ‖(heckePol n q a).coeff i - algebraMap c.O (Qbar l) b'‖ < 1 := by
  have e : ∀ j ≤ n, ‖(heckePol n q a).coeff (n - j) - algebraMap c.O (Qbar l) ((heckePol n q b).coeff (n - j))‖ =
      ‖a j - algebraMap c.O (Qbar l) (b j)‖ := fun j hj => by
    rw [← coeff_map, JEx.heckePol_map, hecke_poly_coeff_formula _ _ _ _ hj, hecke_poly_coeff_formula _ _ _ _ hj, ← mul_sub]
    simp [hq]
  rw [← JEx.heckePol_map]
  constructor
  · intro h i b' hb
    rw [coeff_map] at hb
    have h1 : ‖algebraMap c.O (Qbar l) ((heckePol n q b).coeff i) - algebraMap c.O (Qbar l) b'‖ < 1 := by
      rw [← map_sub]
      exact norm_lt_one_of_residue_zero c _ (by rw [map_sub, hb, sub_self])
    have h2 : ‖(heckePol n q a).coeff i - algebraMap c.O (Qbar l) ((heckePol n q b).coeff i)‖ < 1 := by
      rcases le_or_gt i n with hi | hi
      · have := e (n - i) (Nat.sub_le _ _)
        rw [Nat.sub_sub_self hi] at this
        rw [this]
        exact h _ (Nat.sub_le _ _)
      · rw [hecke_poly_coeff_zero _ _ _ _ hi, hecke_poly_coeff_zero _ _ _ _ hi]
        simp
    rw [← sub_add_sub_cancel _ (algebraMap c.O (Qbar l) ((heckePol n q b).coeff i))]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h2 h1)
  · intro h j hj
    rw [← e j hj]
    exact h _ _ (coeff_map _ _).symm

private theorem hecke_part_frobenius {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hH : H.Ax) (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
    {ξ : GV n H.Sl →* GL (Fin d) ℂ} (Y : H.Part ι lam ξ) (a : H.Op → c.O) (w : H.Wp) (B : ValuationSubring Ω) (σ : G L Ω)
    (hB : IsPlaceOver B w.1) (hσ : IsFrob B (normV w.1) σ) :
    (∀ k : Fin n, ‖ι.symm (Y.a w (k + 1)) - algebraMap c.O (Qbar l) (a (.inl (w, k)))‖ < 1) ↔
      ∀ (i : ℕ) (b : c.O), residue c.O b = (heckePol n (normV w.1) fun j =>
          if h : 0 < j ∧ j - 1 < n then residue c.O (a (.inl (w, ⟨j - 1, h.2⟩))) else 1).coeff i →
        ‖(Y.r (H.prj σ⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i - algebraMap c.O (Qbar l) b‖ < 1 := by
  have hq : ‖((normV w.1 : ℕ) : Qbar l)‖ = 1 := by
    have h0 := (cycZ L Ω l σ).isUnit
    rw [cycZ_of_isFrob (hH.Wp_away w.1 w.2) hB hσ, PadicInt.isUnit_iff] at h0
    rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap', ← h0, PadicInt.norm_def, PadicInt.coe_natCast]
  have e : (Y.r (H.prj σ⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly = heckePol n (normV w.1) fun j => ι.symm (Y.a w j) := by
    refine Polynomial.map_injective ι.toRingHom ι.injective ?_
    rw [Y.frob w B σ hB hσ, JEx.heckePol_map]
    simp
  have e2 : (fun j => if h : 0 < j ∧ j - 1 < n then residue c.O (a (.inl (w, ⟨j - 1, h.2⟩))) else 1) =
      fun j => residue c.O (if h : 0 < j ∧ j - 1 < n then a (.inl (w, ⟨j - 1, h.2⟩)) else 1) := by
    funext j
    split_ifs
    · rfl
    · exact (map_one _).symm
  rw [e, e2, ← hecke_poly_coeff_congruence_iff c n _ hq]
  constructor
  · intro h j hj
    rcases j with _ | j
    · rw [Y.a_zero, dite_eq_right (by omega)]
      simp
    · rw [dite_eq_left ⟨Nat.succ_pos _, hj⟩]
      exact h ⟨j, hj⟩
  · intro h k
    have := h (k + 1) k.2
    rw [dite_eq_left ⟨Nat.succ_pos _, k.2⟩] at this
    exact this

theorem UpperTheory.V.Hi.levelUR2H3Abs :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    IsDomain A → ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.Aut ι P → ∀ lam0 ∈ H.admitted, H.DenseWt θ lam0 → ∀ (a : H.Op → c.O) (K : H.Lev) (φ : H.Gq → (ResidueField c.O)[X]), IsLocallyConstant φ → (∀ (w : H.Wp) (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ → φ (H.prj σ⁻¹) = heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then residue c.O (a (.inl (w, ⟨j - 1, h.2⟩))) else 1) → ∀ (ι' : Type) (j : ι' → H.Op), (∀ x, Sum.inr x ∈ Set.range j) → Dense {g : H.Gq | ∃ w : H.Wp, (∀ k, Sum.inl (w, k) ∈ Set.range j) ∧ ∃ (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 ∧ IsFrob B (normV w.1) σ ∧ g = H.prj σ⁻¹} → locPart (H.X.Ord (H.τA A) θ (H.lev K)) (fun i => H.op A (j i)) (fun i => algebraMap c.O A (a (j i))) = H.MK θ a K := by
  intro _ L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ hA ι P hP lam0 _ hd a K φ hφ hφ2 ι' j hj hD
  obtain ⟨hC, hfi, hfr, -⟩ := hiComm L Ω l n c H hH A θ hθ K
  haveI : Fact (CommOn (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A)) := ⟨hC⟩
  obtain ⟨x, hx⟩ : ∃ x : A →ₐ[c.O] Qbar l, H.Good θ x lam0 := by
    by_contra h
    exact one_ne_zero (hd 1 fun x hx => absurd ⟨x, hx⟩ h)
  obtain ⟨d, ξ, c0, sp, hsp⟩ := spec L Ω l n c H hH A θ hθ ι x lam0 hx.2.1
  refine levelUR2LocSub l c A _ _ ι' _ (H.op A) j a x fun z hz h => ?_
  obtain ⟨Y, hY⟩ := levelUR2OrdPt L Ω l n c H hH A θ hθ ι P hP x lam0 d ξ c0 sp hsp hx.1 K z hz
  have hall := levelUR2GalRes l c H.Gq n Y.r Y.cont φ hφ _ hD (by
    rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
    rw [hφ2 w B σ hB hσ]
    refine (hecke_part_frobenius H hH ι Y a w B σ hB hσ).1 fun k => ?_
    obtain ⟨i, hi⟩ := hw k
    rw [hY, ι.symm_apply_apply, ← hi]
    exact h i)
  rintro (⟨w, k⟩ | y)
  · obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w.1
    obtain ⟨σ, hσ⟩ := exists_isFrob hB
    have := (hecke_part_frobenius H hH ι Y a w B σ hB hσ).2 (by
      rw [← hφ2 w B σ hB hσ]
      exact hall _) k
    rwa [hY, ι.symm_apply_apply] at this
  · obtain ⟨i, hi⟩ := hj y
    rw [← hi]
    exact h i
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2Unr
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem unr_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem unr_sum {M : Type} [AddCommGroup M] [Module ℂ M] {m : ℕ} {H : Type} [Group H] (t : H →* GL (Fin m) ℂ)
    (f : Fin m → M) (i : Fin m) : ∑ j : Fin m, t 1 i j • f j = f i := by
  simp [Matrix.one_apply]

theorem UpperTheory.V.Hi.partUR2Unr :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → IsUnramU σ w := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ _ hY w hw
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hY
  obtain ⟨hB, hσ⟩ := (partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ F).1 hF
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hF0
  have hA : F i ∈ (hset Q τ₀).X.AF ξ := hB.1 i (Set.mem_univ _)
  have h1 := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).1 (F i) hA
  obtain ⟨ℓ, hℓ⟩ := not_forall.1 (mt h1 hi)
  refine ⟨_, hσ i ℓ, hℓ, fun x hx hk => ?_⟩
  have hne : ∀ u : Plc L, u.under (𝓞 (Lp L)) ∈ V.S' → cLoc u x = 1 := fun u hu =>
    GlobalTheory.DefU.LocRet.mem_locU_ne hx fun h => hw (h ▸ hu)
  have hS : ∀ v ∈ s.S, cLoc (s.w v) x = 1 := fun v hv => hne _ ((unr_under s v).symm ▸ V.sub hv)
  have hK : cLoc w x ∈ KO (w.adicCompletion L) (Fin n) := by
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact hk
  have h2 := partUR2Fix l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ F hB x (Subgroup.mem_inf.1 hx).1
    (fun v => hS v.1 (Or.inl v.2)) 1 (fun u => (hS u.1 (Or.inr (Or.inl u.2))).symm)
    (by
      rw [hS s.v0 (Or.inr (Or.inr rfl))]
      exact one_mem _)
    (fun u _ => by
      by_cases h : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · exact UpperTheory.mem_maximalCompact_of_under_eq L n x w u h hK
      · rw [show cLoc u x = 1 from GlobalTheory.DefU.LocRet.mem_locU_ne hx h]
        exact one_mem _)
    (fun q => hne _ (Q.range.ge (Or.inr ⟨q, rfl⟩))) i ℓ
  exact (unr_sum _ (fun j => RU L n x (toForm ι e (F j) ℓ)) i).symm.trans h2
end

