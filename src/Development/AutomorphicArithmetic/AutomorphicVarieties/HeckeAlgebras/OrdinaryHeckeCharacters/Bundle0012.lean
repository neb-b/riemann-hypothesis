module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ClParts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2Compat
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem lc_adic {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R]
    [CommRing R'] [Algebra O R'] [Alg.IsCO O R'] (f : R →ₐ[O] R') {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : Alg.AdicCont (maximalIdeal R) a) : Alg.AdicCont (maximalIdeal R') fun g => f (a g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← Alg.res_eq_zero_iff O, Alg.res_map, Alg.res_eq_zero_iff]
    exact hy
  exact (ha N).comp (Ideal.quotientMap _ (f : R →+* R') hle)

private theorem lc_chi {n : ℕ} {R R' G : Type} [CommRing R] [CommRing R'] [Group G] (D : W.GDet n R G) (f : R →+* R') (g : G) :
    (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f ∧
      ∀ i, (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have h := (CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)
  rwa [MonoidAlgebra.mapRingHom_single, map_one] at h

private theorem lc_pol {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n q : ℕ) (a : ℕ → A) :
    (Hi.heckePol n q a).map f = Hi.heckePol n q fun j => f (a j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Hi.heckePol, Polynomial.map_sum]

section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) {T' T : Type} [CommRing T'] [CommRing T] [Algebra c.O T'] [Algebra c.O T]
    (Φ : T' →ₐ[c.O] T) (v : H.V) (g : Dec (F := L) (H.pl v))

private theorem lc_eps (p : T'ˣ) (i : ℕ) :
    (Units.map Φ.toRingHom.toMonoidHom p * H.epsV T v g ^ i : Tˣ) = Units.map Φ.toRingHom.toMonoidHom (p * H.epsV T' v g ^ i) := by
  rw [map_mul, map_pow]
  congr 2
  exact Units.ext (Φ.commutes _).symm

private theorem lc_unit (p : Dec (F := L) (H.pl v) →* T'ˣ) (i : ℕ) (b' : T') (b : T) (hb : Φ b' = b)
    (h : (p g * H.epsV T' v g ^ i : T'ˣ) * b' = 1) : (W.pushCh Φ.toRingHom p g * H.epsV T v g ^ i : Tˣ) * b = 1 := by
  have e := congrArg Φ h
  rw [map_mul, map_one, hb] at e
  rw [← e]
  exact congrArg (fun u : Tˣ => (u : T) * b) (lc_eps H Φ v g (p g) i)

private theorem lc_unif (p : Fin n → Dec (F := L) (H.pl v) →* T'ˣ) (j : Fin n) (b' : T') (b : T) (hb : Φ b' = b)
    (h : ((∏ i with i ≤ j, p i g * H.epsV T' v g ^ (i : ℕ) : T'ˣ) : T') = b') :
    ((∏ i with i ≤ j, W.pushCh Φ.toRingHom (p i) g * H.epsV T v g ^ (i : ℕ) : Tˣ) : T) = b := by
  rw [← hb, ← h]
  have e : (∏ i with i ≤ j, W.pushCh Φ.toRingHom (p i) g * H.epsV T v g ^ (i : ℕ) : Tˣ) =
      Units.map Φ.toRingHom.toMonoidHom (∏ i with i ≤ j, p i g * H.epsV T' v g ^ (i : ℕ)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => lc_eps H Φ v g (p i g) i
  rw [e]
  rfl

end

private theorem lc_cont {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R]
    [CommRing R'] [Algebra O R'] [Alg.IsCO O R'] (f : R →ₐ[O] R') {n : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    (D : W.GDet n R G) (h : D.IsCont (maximalIdeal R)) : (D.map f.toRingHom).IsCont (maximalIdeal R') := fun i => by
  rw [funext fun g => (lc_chi D f.toRingHom g).2 i]
  exact lc_adic f (h i)

private theorem lc_pcont {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R]
    [CommRing R'] [Algebra O R'] [Alg.IsCO O R'] (f : R →ₐ[O] R') {G : Type} [Group G] [TopologicalSpace G]
    (p : G →* Rˣ) (h : Alg.AdicCont (maximalIdeal R) fun g => (p g : R)) :
    Alg.AdicCont (maximalIdeal R') fun g => (W.pushCh f.toRingHom p g : R') :=
  lc_adic f h

private theorem lc_frob {O : Type} [CommRing O] {R R' : Type} [CommRing R] [Algebra O R]
    [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') {n : ℕ} {G : Type} [Group G]
    (D : W.GDet n R G) (g : G) (q : ℕ) (P : ℕ → Prop) [DecidablePred P] (b : ∀ j, P j → R) (b' : ∀ j, P j → R')
    (hb : ∀ j h, f (b j h) = b' j h)
    (h : D.chi (MonoidAlgebra.single g 1) = Hi.heckePol n q fun j => if h : P j then b j h else 1) :
    (D.map f.toRingHom).chi (MonoidAlgebra.single g 1) = Hi.heckePol n q fun j => if h : P j then b' j h else 1 := by
  rw [(lc_chi D f.toRingHom _).1, h, lc_pol]
  refine congrArg _ (funext fun j => ?_)
  split_ifs
  · exact hb _ _
  · exact map_one _

private theorem lc_comp {O : Type} [CommRing O] {R T' T : Type} [CommRing R] [Algebra O R] [CommRing T'] [Algebra O T']
    [CommRing T] [Algebra O T] (f' : R →ₐ[O] T') (Φ : T' →ₐ[O] T) (f : R →ₐ[O] T) {n : ℕ} {G V : Type} {Γ : V → Type} [Group G]
    [∀ v, Group (Γ v)] (D : W.GDet n R G) (ψ : ∀ v, Fin n → Γ v →* Rˣ)
    (hu : ∀ f g : R →ₐ[O] T, D.map f.toRingHom = D.map g.toRingHom →
      (∀ v i, W.pushCh f.toRingHom (ψ v i) = W.pushCh g.toRingHom (ψ v i)) → f = g)
    (h : D.map f.toRingHom = (D.map f'.toRingHom).map Φ.toRingHom ∧
      (fun v i => W.pushCh f.toRingHom (ψ v i)) = fun v i => W.pushCh Φ.toRingHom (W.pushCh f'.toRingHom (ψ v i))) (t : R) :
    f t = Φ (f' t) := by
  rw [hu f (Φ.comp f') (h.1.trans ((CA.d_gmap D).2.1 _ _)) fun v i => congrFun (congrFun h.2 v) i]
  rfl

set_option maxHeartbeats 1600000 in
private theorem lc_univ {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ)
    (a : H.Op → c.O) (K K' : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)]
    [Fact (CommOn (H.MK θ a K') (H.op A))] [Alg.IsCO c.O (H.TK θ a K')] (Φ : H.TK θ a K' →ₐ[c.O] H.TK θ a K)
    (hΦg : ∀ i, Φ (H.gen θ a K' i) = H.gen θ a K i) (hΦA : ∀ b, Φ (algebraMap A _ b) = algebraMap A _ b)
    (D : W.GDet n (H.TK θ a K') H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K')ˣ)
    (hU : H.IsUniv θ a K' (maximalIdeal _) D ψ) :
    H.IsUniv θ a K (maximalIdeal _) (D.map Φ.toRingHom) fun v i => W.pushCh Φ.toRingHom (ψ v i) := by
  refine { cont := lc_cont Φ D hU.cont, ψ_cont := ?_, frob := ?_, ψ_unit := ?_, ψ_unif := ?_ }
  · intro v i
    exact lc_pcont Φ (ψ v i) (hU.ψ_cont v i)
  · intro w B σ hB hσ
    exact lc_frob Φ D _ _ (fun j => 0 < j ∧ j - 1 < n) _ _ (fun _ _ => hΦg _) (hU.frob w B σ hB hσ)
  · intro v i s g u hg hs
    exact lc_unit H Φ v g (ψ v i) i _ _ (hΦA _) (hU.ψ_unit v i s g u hg hs)
  · intro v j s g hg hs
    exact lc_unif H Φ v g (ψ v) j _ _ (hΦg _) (hU.ψ_unif v j s g hg hs)

set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Hi.levelUR2Compat :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) (K K' : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)] [Fact (CommOn (H.MK θ a K') (H.op A))] [Alg.IsCO c.O (H.TK θ a K')] (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ), (∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T), D₀.map f.toRingHom = D₀.map g.toRingHom → (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = W.pushCh g.toRingHom (ψ₀ v i)) → f = g) → ∀ (f : R →ₐ[c.O] H.TK θ a K) (f' : R →ₐ[c.O] H.TK θ a K'), H.IsMap θ a K D₀ ψ₀ f → H.IsMap θ a K' D₀ ψ₀ f' → ∀ φ : H.MK θ a K →ₗ[A] H.MK θ a K', Function.Injective φ → (∀ i (y : H.MK θ a K), ((φ ((H.gen θ a K i : Module.End A (H.MK θ a K)) y) : H.MK θ a K') : H.X.Fn A H.m) = H.op A i (φ y)) → ∀ t y, φ ((f t : Module.End A (H.MK θ a K)) y) = (f' t : Module.End A (H.MK θ a K')) (φ y) := by
  intro hN L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ hθ a K K' _ _ _ _ R _ _ D₀ ψ₀ huniq f f' hf hf' φ hφ hgen t y
  obtain ⟨Ψ, hΨg, hΨ⟩ := levelUR2HeckeMap A _ _ _ _ (H.MK θ a K) (H.MK θ a K') (H.op A) (H.op A) φ id hφ hgen
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : H.TK θ a K' →ₐ[c.O] H.TK θ a K, ∀ x, Φ x = Ψ x := ⟨Ψ.restrictScalars c.O, fun _ => rfl⟩
  have hM := lc_univ H θ a K K' Φ (fun i => (hΦ _).trans (hΨg i)) (fun b => (hΦ _).trans (Ψ.commutes b)) _ _ hf'
  have e := lc_comp f' Φ f D₀ ψ₀ (huniq _) (coreUniq hN L Ω l n c H hA A θ hθ a K _ _ hM _ _ hf) t
  rw [e, hΦ]
  exact hΨ (f' t) y
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2LevOut
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.levelUR2LevOut :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (K : (hset Q τ₀).Lev) (u : Ub n s), u ∈ (hset Q τ₀).lev K → (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → cmp n w (u : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n)) ∧ ∀ q : Q.Q, cmp n (Q.wq q) (u : Ga l L n) ∈ K.1 q := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀ K u hu
  classical
  have hS : ∀ q : Q.Q, (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := fun q => by
    rw [Q.range]
    exact Or.inr ⟨q, rfl⟩
  have hsec := fun q : Q.Q => (secU l L Ω s n hn (Q.wq q)
    (UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ (hS q)) _ rfl)).2 (Q.notS q)
  have h1 : ∀ (q : Q.Q) (g : GLw n (Q.wq q)) (w : Plc L), w.under (𝓞 (Lp L)) ≠ (Q.wq q).under (𝓞 (Lp L)) →
      CaseU.cmp n w ((sec n s (Q.wq q) g : Ub n s) : Ga l L n) = 1 := fun q g w hw =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ((hsec q).2.2 g) w) hw)
  let P : Subgroup (Ub n s) :=
    (⨅ (w : Plc L) (_ : w.under (𝓞 (Lp L)) ∉ V.S'),
      (KO (w.adicCompletion L) (Fin n)).comap ((CaseU.cmp n w).comp (Ub n s).subtype)) ⊓
    ⨅ q : Q.Q, Subgroup.comap ((CaseU.cmp n (Q.wq q)).comp (Ub n s).subtype) (K.1 q)
  have hP : ∀ x : Ub n s, x ∈ P ↔
      (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → CaseU.cmp n w (x : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n)) ∧
        ∀ q : Q.Q, CaseU.cmp n (Q.wq q) (x : Ga l L n) ∈ K.1 q := fun x =>
    ⟨fun h => ⟨fun w hw => Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 h).1 w) hw,
      fun q => Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 h).2 q⟩,
     fun h => Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => h.1 w hw,
      Subgroup.mem_iInf.2 fun q => h.2 q⟩⟩
  have hle : (hset Q τ₀).lev K ≤ P := by
    refine sup_le (fun x hx => ?_) (iSup_le fun q => ?_)
    · have hx' : x ∈ UQ n Q := hx
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx').1, Subgroup.mem_iInf.2 fun q => ?_⟩
      have e := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx').2 q)
      exact Subgroup.mem_comap.2 (e ▸ one_mem _)
    · rintro _ ⟨g, hg, rfl⟩
      refine (hP (sec n s (Q.wq q) g)).2 ⟨fun w hw => ?_, fun q' => ?_⟩
      · rw [h1 q g w fun h => hw (h ▸ hS q)]
        exact one_mem _
      · by_cases h : q' = q
        · subst h
          exact Set.mem_of_eq_of_mem ((hsec q').2.1 g) hg
        · rw [h1 q g _ fun h' => h (Q.inj h')]
          exact one_mem _
  exact (hP u).1 (hle hu)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2OrdPt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

open TensorProduct in
private theorem op_eig {A K M W ι : Type} [CommRing A] [Field K] [AddCommGroup M] [Module A M]
    [AddCommGroup W] [Module K W] (Y : Submodule A M) [Module.Free A Y] [Module.Finite A Y]
    (op : ι → Module.End A M) [hc : Fact (CommOn Y op)] (χ : A →+* K) (sp : M → W)
    (hadd : ∀ f ∈ Y, ∀ f' ∈ Y, sp (f + f') = sp f + sp f') (hsmul : ∀ f ∈ Y, ∀ b : A, sp (b • f) = χ b • sp f)
    (hind : ∀ (κ : Type) (b : Module.Basis κ A Y), LinearIndependent K fun i => sp (b i))
    (opC : ι → Module.End K W) (hop : ∀ i, ∀ f ∈ Y, sp (op i f) = opC i (sp f))
    (z : heckeAlg Y op →+* K) (hz : z.comp (algebraMap A _) = χ) :
    ∃ F ∈ Submodule.span K (sp '' Y), F ≠ 0 ∧ ∀ i, opC i F = z (heckeGen Y op i) • F := by
  letI : Algebra A K := χ.toAlgebra
  letI : Module A W := Module.compHom W χ
  haveI : IsScalarTower A K W := ⟨fun a k w => mul_smul (χ a) k w⟩
  let s : Y →ₗ[A] W :=
    { toFun := fun f => sp f
      map_add' := fun f g => hadd _ f.2 _ g.2
      map_smul' := fun b f => hsmul _ f.2 b }
  have hs : Function.Injective (s.liftBaseChange K) := by
    let b := Module.Free.chooseBasis A Y
    have h1 : s.liftBaseChange K = Finsupp.linearCombination K (fun i => sp (b i)) ∘ₗ (b.baseChange K).repr.toLinearMap :=
      (b.baseChange K).ext fun i => by
        rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.linearCombination_single,
          Module.Basis.baseChange_apply, LinearMap.liftBaseChange_tmul]
        rfl
    rw [h1, LinearMap.coe_comp]
    exact Function.Injective.comp (hind _ b) (b.baseChange K).repr.injective
  obtain ⟨v, hv, hv'⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.pointEig (M := Y)
    ({ z with commutes' := fun b => RingHom.congr_fun hz b } : heckeAlg Y op →ₐ[A] K)
  refine ⟨s.liftBaseChange K v, ?_, fun h => hv (hs (h.trans (map_zero _).symm)), fun i => ?_⟩
  · have h : s.liftBaseChange K v ∈ LinearMap.range (s.liftBaseChange K) := ⟨v, rfl⟩
    rw [LinearMap.range_liftBaseChange] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨f, rfl⟩
    exact ⟨f, f.2, rfl⟩
  · have h1 : opC i ∘ₗ s.liftBaseChange K =
        s.liftBaseChange K ∘ₗ (Algebra.lsmul A A Y (heckeGen Y op i)).baseChange K := by
      ext y
      simp only [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self, curry_apply, LinearMap.coe_restrictScalars,
        LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, one_smul]
      exact (hop i _ y.2).symm
    have h2 := LinearMap.congr_fun h1 v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hv', map_smul] at h2
    exact h2

theorem UpperTheory.V.Hi.levelUR2OrdPt :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.Aut ι P → ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp → lam ∈ H.admitted → ∀ (K : H.Lev) [Fact (CommOn (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A))] (z : heckeAlg (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) →+* Qbar l), z.comp (algebraMap A _) = x.toRingHom → ∃ Y : H.Part ι lam ξ, ∀ (w : H.Wp) (k : Fin n), Y.a w (k + 1) = ι (z (heckeGen _ (H.op A) (.inl (w, k)))) := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP x lam d ξ c0 sp hsp hlam K _ z hz
  obtain ⟨-, hfin, hfree, -⟩ := hiComm L Ω l n c H hH A θ hθ K
  obtain ⟨F, hF, hF0, h⟩ := op_eig (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) (ι.toRingHom.comp x.toRingHom) sp
    (hsp.add K) (hsp.smul K) (hsp.indep K) (H.opC ι lam d) (hsp.op K) (ι.toRingHom.comp z)
    (by rw [RingHom.comp_assoc, hz])
  rw [hsp.span K c0 le_rfl, (clParts L Ω l n c H hH A θ hθ ι P hP x lam d ξ c0 sp hsp hlam K c0 le_rfl).2] at hF
  obtain ⟨Y, hY⟩ := levelUR2EigPart ℂ _ (H.Wp × Fin n) {Y : H.Part ι lam ξ // P lam Y.r}
    (fun i => H.opC ι lam d (.inl i)) (fun Y => Y.1.Y) (fun Y i => Y.1.a i.1 (i.2 + 1))
    (fun Y i G hG => Y.1.sph i.1 _ G hG) F (SetLike.le_def.1 (iSup_mono fun _ => inf_le_left) hF) hF0
    (fun i => ι (z (heckeGen _ (H.op A) (.inl i)))) (fun i => h (.inl i))
  exact ⟨Y.1, fun w k => congrFun hY (w, k)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.NonemptyUnitaryHeckeParts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem UpperTheory.V.Hi.module_structure_of_commuting {A R P G : Type} [CommRing A] [CommRing R] [AddCommGroup P] [Module A P] [Group G]
    (ρ : Representation A G P) (α : R →+* Module.End A P) (hc : ∀ t g z, α t (ρ g z) = ρ g (α t z)) :
    ∃ (_ : Module R P) (ρR : Representation R G P), (∀ (t : R) (z : P), t • z = α t z) ∧ ∀ g z, ρR g z = ρ g z := by
  letI : Module R P := Module.compHom P α
  have hs : ∀ (t : R) (z : P), t • z = α t z := fun _ _ => rfl
  refine ⟨inferInstance,
    { toFun := fun g =>
        { toFun := fun z => ρ g z
          map_add' := fun x y => map_add _ x y
          map_smul' := fun t z => by rw [hs, RingHom.id_apply, hs, hc] }
      map_one' := by ext z; simp
      map_mul' := fun g h => by ext z; simp }, hs, fun _ _ => rfl⟩

theorem UpperTheory.V.Hi.levelUR2ModPack :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V₀ : s.Lev) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V₀.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : Pa.TWBase (Pa.pairOf B.u) J Empty D) (V : s.Lev) (h : (Pa.globOf r V).Hom (Pa.globOf r V₀)) (q : ℕ) (w : Fin q → Plc L) (rN : Resid (Pa.globOf r V).frame O n), Pa.Glob.Compat h rN (Pa.residOf r) → ∀ (R : Type) [CommRing R] [Algebra O R] [Alg.IsCO O R] (p : Pair rN R) (A : Type) [CommRing A] [Algebra O A] (e : Pa.abelian₂ O Empty D ≃ₐ[O] A) (lam : A →ₐ[O] R), (∀ k, lam (e (MvPowerSeries.X (.inr k))) = algebraMap O R (b.wt.c k) * (p.ψ (b.wt.v k) (b.wt.i k) (b.wt.γ k) : R) - 1) → ∀ β : R →ₐ[O] B.B, p.Maps β.toRingHom ((Pa.pairOf B.u).D.comap h.p₀) (Pa.pairOf B.u).ψ → ∀ (P : Type) [AddCommGroup P] [Module A P] (ρ : Representation A (GV n w) P) (α : R →+* Module.End A P), (∀ a z, α (lam a) z = a • z) → (∀ t g z, α t (ρ g z) = ρ g (α t z)) → Module.Finite A (fixd ρ (Pa.UIw1 l n w)) → ∀ [((Pa.UIw1 l n w).subgroupOf (Pa.UIw n w)).Normal] (ρ' : Representation A (Pa.UIw n w ⧸ (Pa.UIw1 l n w).subgroupOf (Pa.UIw n w)) (fixd ρ (Pa.UIw1 l n w))), (∀ (u : Pa.UIw n w) f, (ρ' (u : Pa.UIw n w ⧸ (Pa.UIw1 l n w).subgroupOf (Pa.UIw n w)) f).1 = ρ u f) → Module.Projective (MonoidAlgebra A (Pa.UIw n w ⧸ (Pa.UIw1 l n w).subgroupOf (Pa.UIw n w))) ρ'.asModule → ∀ eM : fixd ρ (Pa.UK n w) ≃+ b.M, (∀ (t : R) (m m' : fixd ρ (Pa.UK n w)), (m' : P) = α t m → eM m' = β t • eM m) → ∀ ι : Qbar l ≃+* ℂ, (∀ z : P, z ≠ 0 → ∃ (x : R →+* Qbar l) (ρx : (Pa.globOf r V).G₀ →* GL (Fin n) (Qbar l)) (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (π : Representation ℂ (GV n w) Y) (sp : P →+ Y) (σ : ∀ j, SmIrr (GLw n (w j))), sp z ≠ 0 ∧ Continuous ρx ∧ p.D.map x = W.GDet.ofRep (W.mat ρx) ∧ (∀ t y, sp (α t y) = ι (x t) • sp y) ∧ (∀ g y, sp (ρ g y) = π g (sp y)) ∧ (∀ j, IsoSum (π.comp (Pa.atJ n w j)) ⊤ (σ j)) ∧ ∀ j (Bq : ValuationSubring Ω) (hB : IsPlaceOver Bq (w j)) (rc : IrrGL (k := (w j).adicCompletion L) → WD hB), IsRec hB rc → UpperTheory.V.Lev.WO ι (ρx.comp V.pr) (rc (algNorm (σ j)))) → ∃ M : Pa.LevMod b h w, M.Classical := by
  intro l _ L Ω _ _ _ _ _ _ s V₀ O _ _ _ n r B J D b V h q w rN hcomp R _ _ _ p A _ _ e lam hlam β hβ P _ _ ρ α hα hc hfin
    hN ρ' hρ' hproj eM heM ι hcl
  obtain ⟨modR, ρR, hs, hρR⟩ := UpperTheory.V.Hi.module_structure_of_commuting ρ α hc
  letI algL : Algebra (Pa.abelian₂ O Empty D) R := (lam.toRingHom.comp e.toRingEquiv.toRingHom).toAlgebra
  have halg : ∀ a : Pa.abelian₂ O Empty D, algebraMap (Pa.abelian₂ O Empty D) R a = lam (e a) := fun _ => rfl
  haveI towO : IsScalarTower O (Pa.abelian₂ O Empty D) R := IsScalarTower.of_algebraMap_eq fun x => by
    rw [halg, e.commutes, lam.commutes]
  letI modL : Module (Pa.abelian₂ O Empty D) P := Module.compHom P e.toRingEquiv.toRingHom
  have hL : ∀ (a : Pa.abelian₂ O Empty D) (z : P), a • z = e.toRingEquiv a • z := fun _ _ => rfl
  haveI tow : IsScalarTower (Pa.abelian₂ O Empty D) R P := ⟨fun a t z => by
    rw [Algebra.smul_def, halg, mul_smul, hs, hα, hL]; rfl⟩
  obtain ⟨hF, hP⟩ := UpperTheory.V.Hi.levelUR2ProjTr (Pa.abelian₂ O Empty D) A R P (GV n w) e.toRingEquiv hL ρ ρR hρR
    (Pa.UIw n w) (Pa.UIw1 l n w)
  obtain ⟨ρ'', h1, h2⟩ := hP ρ' hρ' hproj
  have hmem : ∀ z : P, z ∈ fixd ρR (Pa.UK n w) ↔ z ∈ fixd ρ (Pa.UK n w) := fun z =>
    forall_congr' fun u => forall_congr' fun _ => by rw [hρR]
  let φ : fixd ρR (Pa.UK n w) ≃+ fixd ρ (Pa.UK n w) :=
    { toFun := fun v => ⟨v.1, (hmem _).1 v.2⟩
      invFun := fun v => ⟨v.1, (hmem _).2 v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let M : Pa.LevMod b h w :=
    { rN := rN
      compat := hcomp
      R := R
      p := p
      segmentWeightExponent := fun k => (halg _).trans (hlam k)
      β := β
      β_pair := hβ
      P := P
      ρ := ρR
      fin := hF hfin
      proj := ⟨hN, ρ'', h1, h2⟩
      eM := φ.trans eM
      eM_smul := fun t m => heM t (φ m) (φ (t • m)) (hs t m.1) }
  refine ⟨M, ι, fun m hm => ?_⟩
  by_contra h0
  obtain ⟨x, ρx, Y, iY, mY, π, sp, σ, hne, hcont, hdet, hsm, hact, hiso, hlg⟩ := hcl m h0
  exact hne (hm
    { θ := x
      rep := ρx
      cont := hcont
      det := hdet
      Y := Y
      π := π
      sp := sp
      sp_smul := fun t y => (congrArg sp (hs t y)).trans (hsm t y)
      sp_act := fun g y => (congrArg sp (hρR g y)).trans (hact g y)
      σ := σ
      iso := hiso
      lg := hlg })
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2AtW
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem w_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem cLoc_ne {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w u : Plc L}
    {x : UA L n} (hx : x ∈ locU n w) (hu : u.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) : cLoc u x = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) hu)

private theorem cmp_of {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L}
    (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) : cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dite_eq_left h]
  rfl

private theorem cmp_loc {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w u : Plc L}
    {x : UA L n} (hx : x ∈ locU n w) (hu : u.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) :
    cmp n u ((away l L n).rangeRestrict x) = 1 := by
  by_cases h : ((l : ℕ) : 𝓞 L) ∉ u.asIdeal
  · rw [cmp_of h]
    exact cLoc_ne hx hu
  · unfold CaseU.cmp
    rw [dite_eq_right h]
    rfl

section

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] (s : HidaSetting l L Ω) {n : ℕ}

private theorem sec_eq (hn : 1 ≤ n) {w : Plc L} (hw : IsSplitAt w) (hS : w.under (𝓞 (Lp L)) ∉ s.S) {x : UA L n}
    (hx : x ∈ locU n w) : ((sec n s w (cLoc w x) : Ub n s) : Ga l L n) = (away l L n).rangeRestrict x := by
  obtain ⟨hb, h1, h2⟩ := (secU l L Ω s n hn w hw).2 hS
  have hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := fun h => hS <| Or.inl <| by
    change algebraMap (𝓞 (Lp L)) (𝓞 L) (l : 𝓞 (Lp L)) ∈ w.asIdeal
    rwa [map_natCast]
  have hU : (away l L n).rangeRestrict x ∈ Ub n s := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun u => ?_, ?_⟩
    · rw [Subgroup.mem_comap, cmp_loc hx (by
        rw [w_under]
        exact fun h => hS (Or.inr (Or.inl (h ▸ u.2))))]
      exact one_mem _
    · rw [Subgroup.mem_comap, cmp_loc hx (by
        rw [w_under]
        exact fun h => hS (Or.inr (Or.inr h.symm)))]
      exact one_mem _
  have hA : (⟨_, hU⟩ : Ub n s) ∈ locA n s w := Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu =>
    MonoidHom.mem_ker.2 (cmp_loc hx hu)
  have h3 : (⟨_, h2 (cLoc w x)⟩ : locA n s w) = ⟨_, hA⟩ := hb.1 ((h1 _).trans (cmp_of hl x).symm)
  exact congrArg (fun y : locA n s w => (y.1 : Ga l L n)) h3

private theorem toKT_sec (hn : 1 ≤ n) {w : Plc L} (hw : IsSplitAt w) (hS : w.under (𝓞 (Lp L)) ∉ s.S) (g : GLw n w) :
    toKT n s (sec n s w g) = 1 := by
  obtain ⟨-, -, h2⟩ := (secU l L Ω s n hn w hw).2 hS
  refine Subtype.ext (funext fun u => ?_)
  exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (h2 g) (s.w u)) (by
    rw [w_under]
    exact fun h => hS (Or.inr (Or.inl (h ▸ u.2)))))

private theorem infRep_fin {s : HidaSetting l L Ω} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {k : UA L n}
    (hk : k ∈ finU (E := L) (n := n)) : infRep (V := V) ι lam k = 1 := by
  have h1 : ∀ τ : L →+* ℂ, cEmb τ k = 1 := fun τ => by
    change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
    rw [MonoidHom.mem_ker.1 hk, map_one]
  change PiTensorProduct.mapMonoidHom (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) =>
    GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb (ι.toRingHom.comp y.res) k)) = 1
  simp only [h1, map_one]
  exact map_one _

end

private theorem raF_one {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {d m : ℕ}
    (τ : X.Ub →* GL (Fin m) ℂ) (u : X.Ub) (hu : τ u = 1) (F : Fin m → X.Fn ℂ d) (i : Fin m) (x : Ga × Gp) :
    X.raF d τ u F i x = F i (x * ((u : Ga), 1)) := by
  funext k
  change X.ra τ u (fun g j => F j g k) x i = _
  rw [X.ra_apply, hu, Units.val_one, Matrix.one_mulVec]

theorem UpperTheory.V.Hi.partUR2AtW :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ w : Plc L, IsSplitAt w → w.under (𝓞 (Lp L)) ∉ s.S → ∀ (j : GLw n w →* UA L n), (∀ g, j g ∈ locU n w) → (∀ g, cLoc w (j g) = g) →
    ∀ (F : Fin m → (hset Q τ₀).X.Fn ℂ d) (g : GLw n w) (i : Fin m) ℓ, toForm ι e ((hset Q τ₀).atW ι d w g F i) ℓ = RU L n (j g) (toForm ι e (F i) ℓ) := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ _ w hw hS j hj1 hj2 F g i ℓ
  funext x
  have h1 : (hset Q τ₀).τC ι (sec n s w g) = 1 := by
    change Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l))) (τ₀ (toKT n s (sec n s w g))) = 1
    rw [toKT_sec s hn hw hS, map_one, map_one]
  have h2 : ((sec n s w g : Ub n s) : Ga l L n) = (away l L n).rangeRestrict (j g) := by
    have := sec_eq s hn hw hS (hj1 g)
    rwa [hj2] at this
  have h3 : ∀ v : V.frame.Vl, cLoc (s.w v.1) (j g) = 1 := fun v => cLoc_ne (hj1 g) (by
    rw [w_under]
    exact fun h => hS (Or.inl (h ▸ v.2)))
  have h4 : infRep (V := V) ι lam (x * j g)⁻¹ = infRep (V := V) ι lam x⁻¹ := by
    rw [mul_inv_rev, map_mul, infRep_fin V ι lam ((finU (E := L) (n := n)).inv_mem (Subgroup.mem_inf.1 (hj1 g)).1), one_mul]
  have h5 : (show Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) from
        ((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x)) *
      (show Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) from (((sec n s w g : Ub n s) : Ga l L n), 1)) =
      ((away l L n).rangeRestrict (x * j g), fun v : V.frame.Vl => cLoc (s.w v.1) (x * j g)) := by
    refine Prod.ext ?_ (funext fun v => ?_)
    · change (away l L n).rangeRestrict x * ((sec n s w g : Ub n s) : Ga l L n) = (away l L n).rangeRestrict (x * j g)
      rw [h2, map_mul]
    · change cLoc (s.w v.1) x * 1 = cLoc (s.w v.1) (x * j g)
      rw [map_mul, h3]
  have h6 := (raF_one (hset Q τ₀).X ((hset Q τ₀).τC ι) (sec n s w g) h1 F i
    ((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x)).trans (congrArg (F i) h5)
  change _ = ℓ (infRep ι lam (x * j g)⁻¹ (e _))
  rw [h4]
  exact congrArg (fun y => ℓ (infRep (V := V) ι lam x⁻¹ (e y))) h6
end

