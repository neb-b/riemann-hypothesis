module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1269
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Bundle0002
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2167
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FrobNNat
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

private theorem frobN_nat (p : ℕ) [Fact p.Prime] {X Y : Scheme.{0}} (hX : (p : Γ(X, ⊤)) = 0) (hY : (p : Γ(Y, ⊤)) = 0)
    (φ : Y ⟶ X) (j : ℕ) : frobN p Y hY j ≫ φ = φ ≫ frobN p X hX j := by
  induction j with
  | zero => simp [frobN]
  | succ j ih =>
    simp only [frobN, Category.assoc, ih]
    rw [← Category.assoc, GlobalTheory.VB.frob_naturality p hX φ hY, Category.assoc]

private theorem rel_mor (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsReduced X] (h : (p : Γ(X, ⊤)) = 0) (f : ℕ) (hf : 0 < f)
    (ψ V g c a q : X ⟶ X) (h1 : frobN p X h f ≫ ψ = a) (h2 : GlobalTheory.VB.frob X p h ≫ V = q) (h3 : a ≫ g = q ≫ c) :
    ψ ≫ frobN p X h (f - 1) ≫ g = V ≫ c := by
  haveI := (UpperTheory.Gal.Ord.epi p X h).2 f
  rw [← cancel_epi (frobN p X h f)]
  obtain ⟨j, rfl⟩ : ∃ j, f = j + 1 := ⟨f - 1, by omega⟩
  have e : frobN p X h (j + 1) = frobN p X h j ≫ GlobalTheory.VB.frob X p h :=
    frobN_nat p h h (GlobalTheory.VB.frob X p h) j |>.symm ▸ rfl
  calc frobN p X h (j + 1) ≫ ψ ≫ frobN p X h (j + 1 - 1) ≫ g
      = (frobN p X h (j + 1) ≫ ψ) ≫ frobN p X h j ≫ g := by simp
    _ = frobN p X h j ≫ a ≫ g := by
        rw [h1, ← Category.assoc, ← frobN_nat p h h a j, Category.assoc]
    _ = frobN p X h j ≫ (GlobalTheory.VB.frob X p h ≫ V) ≫ c := by rw [h3, h2]
    _ = frobN p X h (j + 1) ≫ V ≫ c := by rw [e]; simp

private theorem frobN_mor (p : ℕ) [Fact p.Prime] {k : Type} [Field k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] (j : ℕ) :
    ∃ (ρ : k →+* k) (u : GrpMor (dp0 k) (𝟙 _) A (dp0 k) (𝟙 _) A ρ (spMap ρ) (frobN p A.left (cast_left p k hk A) j)),
      ∀ c, u.pull c = (frobDR p k hk A)^[j] c := by
  induction j with
  | zero =>
    have u : GrpMor (dp0 k) (𝟙 _) A (dp0 k) (𝟙 _) A (RingHom.id k) (spMap (RingHom.id k)) (frobN p A.left (cast_left p k hk A) 0) := by
      rw [GlobalTheory.Cris.spMap_id]
      exact homMor (dp0 k) (𝟙 _) (𝟙 A)
    exact ⟨RingHom.id k, u, fun c ↦ Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)⟩
  | succ j ih =>
    obtain ⟨ρ, u, hu⟩ := ih
    have F := frobMor p k hk A (cast_left p k hk A)
    have K : GrpMor (dp0 k) (𝟙 _) A (dp0 k) (𝟙 _) A ((frobR p k hk).comp ρ) (spMap ((frobR p k hk).comp ρ))
        (frobN p A.left (cast_left p k hk A) (j + 1)) := by
      rw [GlobalTheory.SchRing.spMap_comp']
      exact u.comp F
    refine ⟨_, K, fun c ↦ ?_⟩
    rw [Function.iterate_succ_apply', ← hu]
    exact (GrpMor.pull_pull u F K (fun _ ↦ rfl) rfl c).symm

private theorem act_nat {O : Type} [Ring O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (a : OActN O G) (n : ℕ) :
    a.act (n : O) = (𝟙 G) ^ n := by
  induction n with
  | zero =>
    have := a.add 0 0
    rw [add_zero] at this
    simpa using this
  | succ n ih => rw [Nat.cast_succ, a.add, ih, a.one, pow_succ]

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.rel :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      ∀ (σ τ : k →+* k) (ψ V : o.A.left ⟶ o.A.left) (m : SMor o.A σ ψ) (n : SMor o.A τ V), frobN p o.A.left (cast_left p k hk o.A) f ≫ ψ = (o.act.act (algebraMap (𝓞 D.F) D.O π.a)).left →
      GlobalTheory.VB.frob o.A.left p (cast_left p k hk o.A) ≫ V = ((𝟙 o.A) ^ p : o.A ⟶ o.A).left →
      ∀ y, m.pull ((frobDR p k hk o.A)^[f - 1] (coh o π.g y)) = n.pull (coh o π.c y) := by
  intro p _ D R _ b N _ _ _ k _ _ hk β o i w f _ _ hf π σ τ ψ V m n h1 h2 y
  haveI hg := o.act.hom (algebraMap (𝓞 D.F) D.O π.g)
  haveI hc := o.act.hom (algebraMap (𝓞 D.F) D.O π.c)
  haveI : Smooth o.A.hom := o.ab.smooth
  haveI : IsReduced o.A.left := GlobalTheory.isReduced_of_smooth_of_isReduced o.A.hom
  obtain ⟨ρ, u, hu⟩ := frobN_mor p hk o.A (f - 1)
  have gm := homMor (dp0 k) (𝟙 _) (o.act.act (algebraMap (𝓞 D.F) D.O π.g))
  have cm := homMor (dp0 k) (𝟙 _) (o.act.act (algebraMap (𝓞 D.F) D.O π.c))
  have h3 : o.act.act (algebraMap (𝓞 D.F) D.O π.a) ≫ o.act.act (algebraMap (𝓞 D.F) D.O π.g) =
      ((𝟙 o.A) ^ p : o.A ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O π.c) := by
    rw [← act_nat o.act p, ← o.act.mul, ← o.act.mul]
    congr 1
    rw [← map_mul, ← map_natCast (algebraMap (𝓞 D.F) D.O) p, ← map_mul, mul_comm π.g, π.prod, mul_comm]
  have hmor := rel_mor p (cast_left p k hk o.A) f hf ψ V _ _ _ _ h1 h2 (congrArg (·.left) h3)
  have K1 := gm.comp u
  have K2 := cm.comp n
  have hring : σ.comp ρ = τ := by
    have e1 : (ψ ≫ frobN p o.A.left (cast_left p k hk o.A) (f - 1) ≫ (o.act.act (algebraMap (𝓞 D.F) D.O π.g)).left) ≫ o.A.hom =
        o.A.hom ≫ spMap σ ≫ spMap ρ := by
      rw [Category.assoc, Category.assoc, Over.w, u.w, ← Category.assoc, m.w, Category.assoc]
    have e2 : (V ≫ (o.act.act (algebraMap (𝓞 D.F) D.O π.c)).left) ≫ o.A.hom = o.A.hom ≫ spMap τ := by
      rw [Category.assoc, Over.w, n.w]
    have e3 : o.A.hom ≫ spMap σ ≫ spMap ρ = o.A.hom ≫ spMap τ :=
      e1.symm.trans ((congrArg (· ≫ o.A.hom) hmor).trans e2)
    have e := (MonObj.one : 𝟙_ (Over (Spec (.of k))) ⟶ o.A)
    have e4 : e.left ≫ o.A.hom = 𝟙 _ := Over.w e
    have e5 : spMap σ ≫ spMap ρ = spMap τ := by
      have := congrArg (e.left ≫ ·) e3
      simpa only [← Category.assoc, e4, Category.id_comp] using this
    apply GlobalTheory.SchRing.spMap_inj
    rw [GlobalTheory.SchRing.spMap_comp']
    exact e5
  rw [← hu]
  exact (congrArg m.pull (GrpMor.pull_pull gm u K1 (fun _ ↦ rfl) rfl y)).trans
    ((GrpMor.pull_pull K1 m K2 (fun r ↦ DFunLike.congr_fun hring r) hmor y).trans
      (GrpMor.pull_pull cm n K2 (fun _ ↦ rfl) rfl y).symm)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FromSpecEv
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private lemma ev_comp {T T' : Type} [CommRing T] [CommRing T'] (g : T →+* T') {Y : Scheme.{0}} (U : Y.Opens)
    (f : Sp T ⟶ Y) (h : ⊤ ≤ f ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap g ≫ f) ⁻¹ᵁ U) :
    (spMap g ≫ f).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of T')).hom =
      (f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom) ≫ CommRingCat.ofHom g := by
  rw [← Scheme.Hom.appLE_comp_appLE (spMap g) f U ⊤ ⊤ h (by simp), Category.assoc, Category.assoc]
  congr 1
  have hh : (spMap g).appLE ⊤ ⊤ (by simp) = (spMap g).appTop := by
    simp [Scheme.Hom.appLE]
    exact Category.comp_id _
  rw [hh]
  exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)

private lemma fromSpec_ev {X : Scheme.{0}} {V W : X.Opens} (hV : IsAffineOpen V) (hVW : V ≤ W)
    (e : ⊤ ≤ hV.fromSpec ⁻¹ᵁ W) :
    hV.fromSpec.appLE W ⊤ e ≫ (Scheme.ΓSpecIso Γ(X, V)).hom = X.presheaf.map (homOfLE hVW).op := by
  have e' : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  rw [← Scheme.Hom.map_appLE hV.fromSpec e' (homOfLE hVW).op, Category.assoc]
  have key : hV.fromSpec.appLE V ⊤ e' ≫ (Scheme.ΓSpecIso Γ(X, V)).hom = 𝟙 _ := by
    simp only [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc]
    rw [← Functor.map_comp_assoc]
    have hid : ∀ i : Opposite.op (⊤ : (Spec Γ(X, V)).Opens) ⟶ Opposite.op ⊤, i = 𝟙 _ :=
      fun i => Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [hid (_ ≫ _), CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  rw [key, Category.comp_id]

private lemma snd_zero {k : Type} [Field k] {X Y : Scheme.{0}} (ψ : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (hV : V ≤ ψ ⁻¹ᵁ U) (hA : IsAffineOpen V) (φ : Γ(X, V) →+* DualNumber k)
    (hc : IsConst (spMap φ ≫ hA.fromSpec ≫ ψ)) (t : Γ(Y, U)) :
    TrivSqZeroExt.snd (φ (X.presheaf.map (homOfLE hV).op (ψ.app U t))) = 0 := by
  have h0 : ⊤ ≤ hA.fromSpec ⁻¹ᵁ (ψ ⁻¹ᵁ U) :=
    hA.fromSpec_preimage_self.ge.trans
      ((TopologicalSpace.Opens.map hA.fromSpec.base).map (homOfLE hV)).le
  have h1 : ⊤ ≤ (hA.fromSpec ≫ ψ) ⁻¹ᵁ U := h0
  have h2 : ⊤ ≤ (spMap φ ≫ hA.fromSpec ≫ ψ) ⁻¹ᵁ U := fun x _ => h1 (Set.mem_univ _)
  have hc' : spMap ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) ≫
      spMap φ ≫ hA.fromSpec ≫ ψ = spMap φ ≫ hA.fromSpec ≫ ψ := hc
  have hcongr : ∀ (w₁ w₂ : Sp (DualNumber k) ⟶ Y), w₁ = w₂ → ∀ (e₁ : ⊤ ≤ w₁ ⁻¹ᵁ U)
      (e₂ : ⊤ ≤ w₂ ⁻¹ᵁ U), w₁.appLE U ⊤ e₁ = w₂.appLE U ⊤ e₂ := by
    rintro _ _ rfl _ _
    rfl
  have A := ev_comp ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom)
    U (spMap φ ≫ hA.fromSpec ≫ ψ) h2 (hc'.symm ▸ h2)
  rw [hcongr _ _ hc' _ h2] at A
  have B := ev_comp φ U (hA.fromSpec ≫ ψ) h1 h2
  have C := fromSpec_ev hA hV h0
  have B' : (spMap φ ≫ hA.fromSpec ≫ ψ).appLE U ⊤ h2 ≫
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom =
      ψ.app U ≫ X.presheaf.map (homOfLE hV).op ≫ CommRingCat.ofHom φ := by
    rw [B, Scheme.Hom.comp_appLE, Category.assoc, Category.assoc]
    erw [← Category.assoc (hA.fromSpec.appLE _ _ _), C]
  have A' := ConcreteCategory.congr_hom A t
  rw [B'] at A'
  have hxx : φ (X.presheaf.map (homOfLE hV).op (ψ.app U t)) =
      ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom)
        (φ (X.presheaf.map (homOfLE hV).op (ψ.app U t))) := by
    simpa using A'
  rw [hxx, RingHom.comp_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]

theorem UpperTheory.Gal.Ord.dzero :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (X Y : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [Smooth s] (ψ : X ⟶ Y),
      (∀ v : Sp (DualNumber k) ⟶ X, v ≫ s = spMap (algebraMap k (DualNumber k)) → IsConst (v ≫ ψ)) →
      ∀ (U : Y.Opens) (t : Γ(Y, U)), ∃ r : Γ(X, ψ ⁻¹ᵁ U), r ^ p = ψ.app U t := by
  intro p _ k _ _ hk X Y _ s _ ψ hψ U t
  have hp : (p : Γ(X, ⊤)) = 0 := by
    have h := congrArg (GlobalTheory.CechDR.secMap s ⊤).hom hk
    rwa [map_natCast, map_zero] at h
  refine rootGlue p X hp (ψ ⁻¹ᵁ U) (ψ.app U t) ?_
  intro V hV hA
  let V' : X.affineOpens := ⟨V, hA⟩
  haveI hsm : Algebra.Smooth k (GlobalTheory.CechDR.Sec s V) := by
    have hi : Smooth hA.fromSpec := inferInstance
    have h0 : Smooth (hA.fromSpec ≫ s) := MorphismProperty.comp_mem _ _ _ hi ‹Smooth s›
    have h1 : Smooth (GlobalTheory.CechDR.affPt s V' ≫ s) := h0
    rw [GlobalTheory.CechDR.affPt_w] at h1
    exact RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp h1)
  haveI : _root_.IsReduced (GlobalTheory.CechDR.Sec s V) := IsReduced.component_reduced V
  have hD := dz1 k (GlobalTheory.CechDR.Sec s V) (X.presheaf.map (homOfLE hV).op (ψ.app U t)) ?_
  · exact _root_.GlobalTheory.ConjSeq.sec_exists_pow_of_D_eq_zero p k hk X s V' _ hD
  intro v
  have hw : (spMap v.toRingHom ≫ hA.fromSpec) ≫ s = spMap (algebraMap k (DualNumber k)) := by
    change spMap v.toRingHom ≫ GlobalTheory.CechDR.affPt s V' ≫ s = _
    rw [GlobalTheory.CechDR.affPt_w, ← Geo.Tor.spMap_comp]
    exact congrArg spMap v.comp_algebraMap
  have hc : IsConst (spMap v.toRingHom ≫ hA.fromSpec ≫ ψ) := by
    convert hψ _ hw using 1
    exact (Category.assoc _ _ _).symm
  exact snd_zero ψ hV hA v.toRingHom hc t
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.RootMor
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

theorem UpperTheory.Gal.Ord.rootMor :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (σ σ' : k →+* k) (ψ ψ' : A.left ⟶ A.left), SMor A σ ψ → (∀ x, σ' x ^ p = σ x) →
      GlobalTheory.VB.frob A.left p (cast_left p k hk A) ≫ ψ' = ψ → SMor A σ' ψ' := by
  intro p _ k _ _ hk A _ _ hAb σ σ' ψ ψ' hS hpow hfr
  haveI := hAb
  haveI : Smooth A.hom := IsAbelianScheme.smooth
  haveI : AlgebraicGeometry.IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  haveI hP : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hAb hAb
  haveI : Smooth (A ⊗ A).hom := IsAbelianScheme.smooth
  haveI : AlgebraicGeometry.IsReduced (A ⊗ A).left :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (A ⊗ A).hom
  haveI : Epi (GlobalTheory.VB.frob A.left p (cast_left p k hk A)) := (epi p A.left (cast_left p k hk A)).1
  haveI : Epi (GlobalTheory.VB.frob (A ⊗ A).left p (cast_left p k hk (A ⊗ A))) :=
    (epi p (A ⊗ A).left (cast_left p k hk (A ⊗ A))).1
  have hσ : spMap (frobR p k hk) ≫ spMap σ' = spMap σ := by
    rw [← Geo.Tor.spMap_comp]
    congr 1
    ext x
    rw [RingHom.comp_apply, GlobalTheory.ConjSeq.frobR_apply, hpow]
  have hw' : ψ' ≫ A.hom = A.hom ≫ spMap σ' := by
    apply (cancel_epi (GlobalTheory.VB.frob A.left p (cast_left p k hk A))).mp
    rw [← Category.assoc, hfr, hS.w, ← Category.assoc,
      GlobalTheory.ConjSeq.frob_comp_hom p k hk A.hom (cast_left p k hk A), Category.assoc, hσ]
  have hnat : ∀ f : (A ⊗ A).left ⟶ A.left,
      GlobalTheory.VB.frob (A ⊗ A).left p (cast_left p k hk (A ⊗ A)) ≫ f ≫ ψ' = f ≫ ψ := by
    intro f
    rw [← Category.assoc, GlobalTheory.VB.frob_naturality p (cast_left p k hk A) f (cast_left p k hk (A ⊗ A)),
      Category.assoc, hfr]
  let F : Over.mk ((A ⊗ A).hom ≫ spMap σ) ⟶ Over.mk ((A ⊗ A).hom ≫ spMap σ') :=
    Over.homMk (GlobalTheory.VB.frob (A ⊗ A).left p (cast_left p k hk (A ⊗ A))) (by
      simp only [Over.mk_hom]
      rw [← Category.assoc,
        GlobalTheory.ConjSeq.frob_comp_hom p k hk (A ⊗ A).hom (cast_left p k hk (A ⊗ A)), Category.assoc, hσ])
  let u : ∀ g : A ⊗ A ⟶ A, Over.mk ((A ⊗ A).hom ≫ spMap σ') ⟶ A := fun g =>
    Over.homMk (g.left ≫ ψ') (by
      simp only [Over.mk_hom]
      rw [Category.assoc, hw', ← Category.assoc, Over.w g])
  let v : ∀ g : A ⊗ A ⟶ A, Over.mk ((A ⊗ A).hom ≫ spMap σ) ⟶ A := fun g =>
    Over.homMk (g.left ≫ ψ) (by
      simp only [Over.mk_hom]
      rw [Category.assoc, hS.w, ← Category.assoc, Over.w g])
  have hFu : ∀ g : A ⊗ A ⟶ A, F ≫ u g = v g := by
    intro g
    apply Over.OverMorphism.ext
    simp only [F, u, v, Over.comp_left, Over.homMk_left]
    exact hnat g.left
  have huniv : (u (fst A A) * u (snd A A)).left = (fst A A * snd A A).left ≫ ψ' := by
    apply (cancel_epi (GlobalTheory.VB.frob (A ⊗ A).left p (cast_left p k hk (A ⊗ A)))).mp
    rw [hnat]
    have e1 : (F ≫ (u (fst A A) * u (snd A A))).left = (v (fst A A) * v (snd A A)).left := by
      rw [MonObj.comp_mul, hFu, hFu]
    rw [Over.comp_left] at e1
    exact e1.trans (hS.mul (A ⊗ A) (fst A A) (snd A A) (v (fst A A)) (v (snd A A)) rfl rfl)
  refine GlobalTheory.DeRham.GrpMor.mk (isDPMorphism_of_eq_bot (dp0 k) rfl (dp0 k) σ') (by simp) hw' ?_
  intro T x y x₀ y₀ hx0 hy0
  let h : T ⟶ A ⊗ A := lift x y
  let hh : Over.mk (T.hom ≫ spMap σ') ⟶ Over.mk ((A ⊗ A).hom ≫ spMap σ') :=
    Over.homMk h.left (by
      simp only [Over.mk_hom]
      rw [← Category.assoc, Over.w h])
  have ex : x₀ = hh ≫ u (fst A A) := by
    apply Over.OverMorphism.ext
    simp only [hh, u, Over.comp_left, Over.homMk_left]
    rw [hx0, ← Category.assoc, ← Over.comp_left, lift_fst]
  have ey : y₀ = hh ≫ u (snd A A) := by
    apply Over.OverMorphism.ext
    simp only [hh, u, Over.comp_left, Over.homMk_left]
    rw [hy0, ← Category.assoc, ← Over.comp_left, lift_snd]
  rw [ex, ey, ← MonObj.comp_mul, Over.comp_left, huniv]
  simp only [hh, Over.homMk_left]
  rw [← Category.assoc, ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]
end

