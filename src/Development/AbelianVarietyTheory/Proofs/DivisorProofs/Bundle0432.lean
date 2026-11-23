module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionMultiplicationChainMap
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.UnitMul
open ClsSpec

variable {R : Type} [CommRing R]

theorem glue_sec (F G : Shv R) (Rel : ∀ U : Scheme.{0}, Sec F U → Sec G U → Prop)
    (hex : ∀ (U : Scheme.{0}) (x : Sec F U), Loc U fun V g => ∃ s, Rel V (Sec.res g x) s)
    (hres : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sec F U) (s : Sec G U), Rel U x s → Rel V (Sec.res g x) (Sec.res g s))
    (huniq : ∀ (U : Scheme.{0}) (x : Sec F U) (s s' : Sec G U), Rel U x s → Rel U x s' → s = s') :
    ∃ a : ∀ U : Scheme.{0}, Sec F U → Sec G U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sec F U), Sec.res g (a U x) = a V (Sec.res g x)) ∧
      ∀ (U : Scheme.{0}) (x : Sec F U) (s : Sec G U), Rel U x s → a U x = s := by
  have key : ∀ (U : Scheme.{0}) (x : Sec F U), ∃ a : Sec G U,
      ∀ (V : Scheme.{0}) (g : V ⟶ U) (s : Sec G V), Rel V (Sec.res g x) s → Sec.res g a = s := by
    intro U x
    obtain ⟨S, hS, hP⟩ := hex U x
    choose s hs using hP
    obtain ⟨a, ha⟩ := (_root_.GlobalTheory.EtC.sec_ext_glue R G U).2 S hS s (fun V W g k hg => by
      refine huniq W (Sec.res (k ≫ g) x) _ _ ?_ (hs _ _ _)
      rw [← res_comp]
      exact hres _ _ _ _ _ (hs _ _ hg))
    refine ⟨a, fun V g s' hs' => sep ⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W k hk => ?_⟩⟩
    beta_reduce
    rw [res_comp, ha W (k ≫ g) hk]
    refine huniq W (Sec.res (k ≫ g) x) _ _ (hs _ _ _) ?_
    rw [← res_comp]
    exact hres _ _ _ _ _ hs'
  choose a ha using key
  refine ⟨a, fun V U g x => sep (ClsSpec.loc_mono (hex V (Sec.res g x)) ?_), fun U x s hs => ?_⟩
  · rintro W k ⟨s, hs⟩
    rw [ha V _ W k s hs, res_comp]
    exact ha U x W (k ≫ g) s (by rwa [← res_comp])
  · rw [← res_id (a U x)]
    exact ha U x U (𝟙 U) s (by rwa [res_id])

variable {q : ℕ} [NeZero q] {i k : ℤ} (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)))
  {D : Cx (ZMod q)} (ι : D ⟶ res _ (tw q i))

def Good (s : ℤ) {U : Scheme.{0}} (b : Sec (D.X s) U) (c : Sec ((res _ (tw q k)).X s) U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U), (∀ ζ : Prim q Γ(V, ⊤),
    Sec.res g c = μ.mul V 0 s s (zero_add s) (resGen 0 ζ) (Sec.map (ι.f s) (Sec.res g b))) ∧
    (Sec.map (ι.f s) (Sec.res g b) = 0 → Sec.res g c = 0)

theorem good_res {s : ℤ} {V U : Scheme.{0}} (g : V ⟶ U) {b : Sec (D.X s) U} {c : Sec ((res _ (tw q k)).X s) U}
    (h : Good μ ι s b c) : Good μ ι s (Sec.res g b) (Sec.res g c) := by
  intro W l
  rw [res_comp, res_comp]
  exact h W (l ≫ g)

theorem good_prim (s : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (b : Sec (D.X s) U) :
    Good μ ι s b (μ.mul U 0 s s (zero_add s) (resGen 0 ζ) (Sec.map (ι.f s) b)) := by
  intro V g
  refine ⟨fun ξ => ?_, fun h0 => ?_⟩
  · rw [μ.nat, res_resGen, res_map, resGen_zero_eq ξ (ζ.map g.appTop.hom)]
  · rw [μ.nat, res_map, h0, map_zero]

theorem good_zero (s : ℤ) {U : Scheme.{0}} (b : Sec (D.X s) U) (h : Sec.map (ι.f s) b = 0) : Good μ ι s b 0 := by
  intro V g
  rw [res_zero]
  refine ⟨fun ξ => ?_, fun _ => rfl⟩
  rw [← res_map, h, res_zero, map_zero]

variable {ι} in
theorem localization₂ (hD : ∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔
      Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0)
    {s : ℤ} {U : Scheme.{0}} (b : Sec (D.X s) U) :
    Loc U fun V g => Nonempty (Prim q Γ(V, ⊤)) ∨ Sec.map (ι.f s) (Sec.res g b) = 0 := by
  have h1 := (hD s U (Sec.map (ι.f s) b)).1 ⟨b, rfl⟩
  refine ClsSpec.loc_trans (ClsSpec.loc_mono h1 fun V g h => ?_)
  rcases h with hu | h0
  · exact ClsSpec.loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).1 hu) fun W l ⟨ζ⟩ => Or.inl ⟨ζ⟩
  · rw [res_map] at h0
    exact GlobalTheory.T.etaleLocal_property_calculus_rules.1 V _ fun W l => Or.inr (by rw [← res_comp, ← res_map, h0, res_zero])

end GlobalTheory.EtC.UnitMul

namespace GlobalTheory.EtC.UnitMul
open ClsSpec

variable {R : Type} [CommRing R]

variable {q : ℕ} [NeZero q] {i k : ℤ} (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)))
  {D : Cx (ZMod q)} (ι : D ⟶ res _ (tw q i))

theorem res_smul {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (r : ULift.{1} R) (a : Sec F U) :
    Sec.res g (r • a) = r • Sec.res g a := map_smul _ _ _
theorem smap_smul {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (r : ULift.{1} R) (a : Sec F U) :
    Sec.map φ (r • a) = r • Sec.map φ a := map_smul _ _ _

variable {ι} in
theorem good_uniq (hD : ∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔
      Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0)
    {s : ℤ} {U : Scheme.{0}} (b : Sec (D.X s) U) (c c' : Sec ((res _ (tw q k)).X s) U)
    (hc : Good μ ι s b c) (hc' : Good μ ι s b c') : c = c' :=
  sep (ClsSpec.loc_mono (localization₂ hD b) fun V g h => h.elim (fun ⟨ζ⟩ => ((hc V g).1 ζ).trans ((hc' V g).1 ζ).symm)
    (fun h0 => ((hc V g).2 h0).trans ((hc' V g).2 h0).symm))


variable {ι} in
theorem exists_fam (hD : ∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔
      Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0) (s : ℤ) :
    ∃ a : ∀ U : Scheme.{0}, Sec (D.X s) U → Sec ((res _ (tw q k)).X s) U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sec (D.X s) U), Sec.res g (a U x) = a V (Sec.res g x)) ∧
      ∀ (U : Scheme.{0}) (x : Sec (D.X s) U) (c : Sec ((res _ (tw q k)).X s) U), Good μ ι s x c → a U x = c :=
  glue_sec _ _ (fun U x c => Good μ ι s x c)
    (fun U x => ClsSpec.loc_mono (localization₂ hD x) fun V g h => h.elim (fun ⟨ζ⟩ => ⟨_, good_prim μ ι s ζ _⟩)
      (fun h0 => ⟨0, good_zero μ ι s _ h0⟩))
    (fun V U g x c h => good_res μ ι g h)
    (fun U x c c' h h' => good_uniq μ hD x c c' h h')

end GlobalTheory.EtC.UnitMul


open GlobalTheory.EtC.UnitMul ClsSpec in
theorem GlobalTheory.EtC.unit_mul_chain_map : ∀ (q : ℕ) [NeZero q] (i k : ℤ) (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)))
    (D : Cx (ZMod q)) (ι : D ⟶ res _ (tw q i)), (∀ n U (a : Sec ((res _ (tw q i)).X n) U),
      (∃ b, Sec.map (ι.f n) b = a) ↔ Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0) →
    ∃ u : D ⟶ res _ (tw q k), ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (s : ℤ) (b : Sec (D.X s) U),
      Sec.map (u.f s) b = μ.mul U 0 s s (zero_add s) (resGen 0 ζ) (Sec.map (ι.f s) b) := by
  intro q _ i k μ D ι hD
  choose a ha hs using exists_fam μ hD
  have aP : ∀ (s : ℤ) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (x : Sec (D.X s) U),
      a s U x = μ.mul U 0 s s (zero_add s) (resGen 0 ζ) (Sec.map (ι.f s) x) :=
    fun s U ζ x => hs s U x _ (good_prim μ ι s ζ x)
  have aZ : ∀ (s : ℤ) (U : Scheme.{0}) (x : Sec (D.X s) U), Sec.map (ι.f s) x = 0 → a s U x = 0 :=
    fun s U x h => hs s U x 0 (good_zero μ ι s x h)
  have aAdd : ∀ (s : ℤ) (U : Scheme.{0}) (x y : Sec (D.X s) U), a s U (x + y) = a s U x + a s U y := by
    intro s U x y
    refine sep (ClsSpec.loc_mono (ClsSpec.loc_and (localization₂ hD x) (localization₂ hD y)) fun V g h => ?_)
    rw [res_add, ha, ha, ha, res_add]
    rcases h with ⟨⟨⟨ζ⟩⟩ | hx, ⟨⟨ζ⟩⟩ | hy⟩
    · rw [aP s V ζ, aP s V ζ, aP s V ζ, smap_add, map_add (f := _)]
    · rw [aP s V ζ, aP s V ζ, aP s V ζ, smap_add, map_add (f := _)]
    · rw [aP s V ζ, aP s V ζ, aP s V ζ, smap_add, map_add (f := _)]
    · rw [aZ s V _ hx, aZ s V _ hy, aZ s V _ (by rw [smap_add, hx, hy, add_zero]), add_zero]
  have aSmul : ∀ (s : ℤ) (U : Scheme.{0}) (r : ULift.{1} (ZMod q)) (x : Sec (D.X s) U), a s U (r • x) = r • a s U x := by
    intro s U r x
    refine sep (ClsSpec.loc_mono (localization₂ hD x) fun V g h => ?_)
    rw [res_smul, ha, ha, res_smul]
    rcases h with ⟨⟨ζ⟩⟩ | hx
    · rw [aP s V ζ, aP s V ζ, smap_smul, map_smul]
    · rw [aZ s V _ hx, aZ s V _ (by rw [smap_smul, hx, smul_zero]), smul_zero]
  have aD : ∀ (s : ℤ) (U : Scheme.{0}) (x : Sec (D.X s) U),
      Sec.map ((res _ (tw q k)).d s (s + 1)) (a s U x) = a (s + 1) U (Sec.map (D.d s (s + 1)) x) := by
    intro s U x
    have hι : ∀ {V : Scheme.{0}} (y : Sec (D.X s) V), Sec.map ((res _ (tw q i)).d s (s + 1)) (Sec.map (ι.f s) y) =
        Sec.map (ι.f (s + 1)) (Sec.map (D.d s (s + 1)) y) := fun y => by
      rw [map_comp, ι.comm, ← map_comp]
    refine sep (ClsSpec.loc_mono (localization₂ hD x) fun V g h => ?_)
    rw [res_map, ha, ha, res_map]
    rcases h with ⟨⟨ζ⟩⟩ | hx
    · rw [aP s V ζ, aP (s + 1) V ζ, μ.leibniz, ← hι]
      have h0 : Sec.map ((res _ (tw q 0)).d 0 (0 + 1)) (resGen 0 ζ) = 0 := d_resGen 0 ζ
      rw [h0, map_zero, LinearMap.zero_apply, zero_add, Int.negOnePow_zero, one_smul]
    · rw [aZ s V _ hx, smap_zero, aZ (s + 1) V _ (by rw [← hι, hx, smap_zero])]
  let F : ∀ s : ℤ, D.X s ⟶ (res _ (tw q k)).X s := fun s =>
    ⟨{ app := fun X => ModuleCat.ofHom
          { toFun := a s X.unop
            map_add' := aAdd s X.unop
            map_smul' := aSmul s X.unop }
       naturality := fun X Y f => by
          apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
          exact (ha s Y.unop X.unop f.unop x).symm }⟩
  refine ⟨{ f := F, comm' := fun s t hst => ?_ }, fun U ζ s b => aP s U ζ b⟩
  change s + 1 = t at hst
  subst hst
  apply Sheaf.hom_ext; ext X x
  exact aD s X.unop x
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalH1SurjectiveUniverses
section
open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.VertSurj

universe a b

theorem surj_of_id {C' : Type b} [Category.{0} C'] {K K' : Cx C'} (m : CxMap K K')
    (hG : m.G = 𝟭 C') (hQ : m.QAll) : Function.Surjective m.h1 := by
  obtain ⟨G, a0, a1, a2, a3, compDegreeZero_natural, compDegreeOne_natural, compDegreeTwo_natural, comp_commutes_diffZero, comp_commutes_diffOne, comp_commutes_diffTwo⟩ := m
  dsimp only at hG
  subst hG
  simp only [Functor.id_obj, Functor.id_map] at compDegreeZero_natural compDegreeOne_natural comp_commutes_diffZero comp_commutes_diffOne
  dsimp only [CxMap.QAll, Functor.id_obj] at hQ
  intro c
  obtain ⟨⟨⟨f', ω'⟩, hc⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hc' : K'.D1 (f', ω') = 0 := hc
  have hA : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
      K'.M0.map ψ (f' T T' φ) - f' T T'' (φ ≫ ψ) + f' T' T'' ψ = 0 :=
    fun T T' T'' φ ψ ↦ congrFun (congrFun (congrFun (congrFun (congrFun (congrArg Prod.fst hc') T) T') T'') φ) ψ
  have hB : ∀ T T' (φ : T ⟶ T'), ω' T' - K'.M1.map φ (ω' T) - K'.d0 T' (f' T T' φ) = 0 :=
    fun T T' φ ↦ congrFun (congrFun (congrFun (congrArg (fun x ↦ x.2.1) hc') T) T') φ
  have hC : ∀ T, K'.d1 T (ω' T) = 0 := fun T ↦ congrFun (congrArg (fun x ↦ x.2.2) hc') T
  choose ω w hω hωw using fun T ↦ (hQ T).surj1 (ω' T) (hC T)

  have hE : ∀ T T' (φ : T ⟶ T'), a1 T' (ω T' - K.M1.map φ (ω T)) =
      K'.d0 T' (f' T T' φ - (w T' - K'.M0.map φ (w T))) := by
    intro T T' φ
    have h1 := hωw T'
    have h2 := hωw T
    have h3 := hB T T' φ
    rw [map_sub, compDegreeOne_natural]
    have e1 : a1 T' (ω T') = ω' T' - K'.d0 T' (w T') := by rw [h1]; abel
    have e2 : a1 T (ω T) = ω' T - K'.d0 T (w T) := by rw [h2]; abel
    rw [e1, e2]; simp only [map_sub]; rw [← K'.diffZero_natural]
    have e3 : ω' T' = K'.M1.map φ (ω' T) + K'.d0 T' (f' T T' φ) := by rw [← sub_eq_zero, ← h3]; abel
    rw [e3]; abel
  choose f₁ hf₁ using fun T T' (φ : T ⟶ T') ↦ (hQ T').inj1 (ω T' - K.M1.map φ (ω T))
    (f' T T' φ - (w T' - K'.M0.map φ (w T)))
    (by rw [map_sub, K.diffOne_natural, hω, hω, map_zero, sub_zero]) (hE T T' φ)
  choose f₂ hf₂0 hf₂ using fun T T' (φ : T ⟶ T') ↦ (hQ T').surj0
    (f' T T' φ - (w T' - K'.M0.map φ (w T)) - a0 T' (f₁ T T' φ))
    (by rw [map_sub, ← comp_commutes_diffZero, hf₁, hE, sub_self])
  have hfa : ∀ T T' (φ : T ⟶ T'), a0 T' (f₁ T T' φ + f₂ T T' φ) =
      f' T T' φ - (w T' - K'.M0.map φ (w T)) := by
    intro T T' φ; rw [map_add (f := _), hf₂]; abel
  have hfd : ∀ T T' (φ : T ⟶ T'), K.d0 T' (f₁ T T' φ + f₂ T T' φ) = ω T' - K.M1.map φ (ω T) := by
    intro T T' φ; rw [map_add (f := _), hf₁, hf₂0, add_zero]
  let f : K.M0.c1 := fun T T' φ ↦ f₁ T T' φ + f₂ T T' φ
  have hfa' : ∀ T T' (φ : T ⟶ T'), a0 T' (f T T' φ) = f' T T' φ - (w T' - K'.M0.map φ (w T)) := hfa
  have hfd' : ∀ T T' (φ : T ⟶ T'), K.d0 T' (f T T' φ) = ω T' - K.M1.map φ (ω T) := hfd
  clear_value f
  have hZ : ((f, ω) : K.T1) ∈ K.Z1 := by
    show K.D1 (f, ω) = 0
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext T T' T'' φ ψ
      show K.M0.map ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = 0
      apply (hQ T'').inj0
      · simp only [map_add (f := _), map_sub, K.diffZero_natural, hfd', K.M1.map_comp]; abel
      · rw [map_add (f := _), map_sub, compDegreeZero_natural, hfa', hfa', hfa']
        simp only [map_sub, K'.M0.map_comp]
        linear_combination (norm := abel1) hA T T' T'' φ ψ
    · funext T T' φ
      show ω T' - K.M1.map φ (ω T) - K.d0 T' (f T T' φ) = 0
      rw [hfd', sub_self]
    · funext T
      exact hω T
  refine ⟨QuotientAddGroup.mk ⟨(f, ω), hZ⟩, ?_⟩
  show QuotientAddGroup.mk (CxMap.z1 _ ⟨(f, ω), hZ⟩) = QuotientAddGroup.mk _
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  refine ⟨w, Prod.ext ?_ ?_⟩
  · funext T T' φ
    show w T' - K'.M0.map φ (w T) = -(a0 T' (f T T' φ)) + f' T T' φ
    rw [hfa']; abel
  · funext T
    show K'.d0 T (w T) = -(a1 T (ω T)) + ω' T
    rw [hωw T]; abel

theorem main : VertHas.{a, b} (fun m ↦ Function.Surjective m.h1) := by
  intro C _ C' _ K K' m hQ
  exact surj_of_id m.vert rfl hQ

theorem instances : VertHas.{1,1} (fun m ↦ Function.Surjective m.h1) ∧
    VertHas.{1,0} (fun m ↦ Function.Surjective m.h1) ∧ VertHas.{0,0} (fun m ↦ Function.Surjective m.h1) :=
  ⟨main, main, main⟩

end GlobalTheory.CxCoh.VertSurj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalH2InjectiveAllUniverses
section
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory.CxCoh

universe a b

theorem cocycle_two_isCoboundary_of_objectwiseQuasiIso {C : Type b} [Category.{0} C] {L K : Cx C}
    (a0 : ∀ T, L.M0.obj T →+ K.M0.obj T) (a1 : ∀ T, L.M1.obj T →+ K.M1.obj T)
    (a2 : ∀ T, L.M2.obj T →+ K.M2.obj T)
    (compDegreeZero_natural : ∀ {T T' : C} (φ : T ⟶ T') x, a0 T' (L.M0.map φ x) = K.M0.map φ (a0 T x))
    (compDegreeOne_natural : ∀ {T T' : C} (φ : T ⟶ T') x, a1 T' (L.M1.map φ x) = K.M1.map φ (a1 T x))
    (comp_commutes_diffZero : ∀ T x, a1 T (L.d0 T x) = K.d0 T (a0 T x))
    (comp_commutes_diffOne : ∀ T x, a2 T (L.d1 T x) = K.d1 T (a1 T x))
    (hq : ∀ T, IsQ (L.d0 T) (L.d1 T) (L.d2 T) (K.d0 T) (K.d1 T) (K.d2 T) (a0 T) (a1 T) (a2 T))
    (z : L.T2) (hz : z ∈ L.Z2) (c' : K.T1)
    (E0 : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
      K.M0.map ψ (c'.1 T T' φ) - c'.1 T T'' (φ ≫ ψ) + c'.1 T' T'' ψ = a0 T'' (z.1 T T' T'' φ ψ))
    (E1 : ∀ T T' (φ : T ⟶ T'),
      c'.2 T' - K.M1.map φ (c'.2 T) - K.d0 T' (c'.1 T T' φ) = a1 T' (z.2.1 T T' φ))
    (E2 : ∀ T, K.d1 T (c'.2 T) = a2 T (z.2.2 T)) :
    ∃ c, L.D1 c = z := by
  obtain ⟨Za, Zb, Zc, Zd⟩ := hz
  choose ω₁ hω₁ using fun T ↦ (hq T).inj2 (z.2.2 T) (c'.2 T) (Zd T) (E2 T).symm
  have h1 : ∀ T, K.d1 T (c'.2 T - a1 T (ω₁ T)) = 0 := fun T ↦ by
    rw [map_sub, E2, ← comp_commutes_diffOne, hω₁, sub_self]
  choose ω₂ w hω₂ hw using fun T ↦ (hq T).surj1 _ (h1 T)
  have hw' : ∀ T, a1 T (ω₂ T) = c'.2 T - a1 T (ω₁ T) - K.d0 T (w T) := fun T ↦ by
    rw [hw T]; abel
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : ∀ T, L.M1.obj T, ∀ T, Ω T = ω₁ T + ω₂ T := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : L.M1.c1, ∀ T T' (φ : T ⟶ T'),
      α T T' φ = z.2.1 T T' φ - (Ω T' - L.M1.map φ (Ω T)) := ⟨_, fun _ _ _ ↦ rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : K.M0.c1, ∀ T T' (φ : T ⟶ T'),
      f T T' φ = c'.1 T T' φ - (w T' - K.M0.map φ (w T)) := ⟨_, fun _ _ _ ↦ rfl⟩
  have hα1 : ∀ T T' (φ : T ⟶ T'), L.d1 T' (α T T' φ) = 0 := fun T T' φ ↦ by
    have hc := Zc T T' φ
    simp only [hα, hΩ, map_sub, map_add (f := _), L.diffOne_natural, hω₁, hω₂, add_zero, map_zero]
    rw [hc]; abel
  have hα2 : ∀ T T' (φ : T ⟶ T'), a1 T' (α T T' φ) = K.d0 T' (-f T T' φ) := fun T T' φ ↦ by
    simp only [hα, hΩ, hf, map_sub, map_add (f := _), map_neg, compDegreeOne_natural, hw', ← E1, K.diffZero_natural]
    abel
  choose g hg using fun T T' (φ : T ⟶ T') ↦
    (hq T').inj1 (α T T' φ) (-f T T' φ) (hα1 T T' φ) (hα2 T T' φ)
  have h3 : ∀ T T' (φ : T ⟶ T'), K.d0 T' (f T T' φ + a0 T' (g T T' φ)) = 0 := fun T T' φ ↦ by
    rw [map_add (f := _), ← comp_commutes_diffZero, hg, hα2, map_neg, add_neg_cancel]
  choose f₂ hf₂ hf₂' using fun T T' (φ : T ⟶ T') ↦ (hq T').surj0 _ (h3 T T' φ)
  refine ⟨(fun T T' φ ↦ f₂ T T' φ - g T T' φ, Ω), Prod.ext (funext fun T ↦ funext fun T' ↦
    funext fun T'' ↦ funext fun φ ↦ funext fun ψ ↦ ?_) (Prod.ext (funext fun T ↦ funext fun T' ↦
    funext fun φ ↦ ?_) (funext fun T ↦ ?_))⟩
  · change L.M0.map ψ (f₂ T T' φ - g T T' φ) - (f₂ T T'' (φ ≫ ψ) - g T T'' (φ ≫ ψ))
      + (f₂ T' T'' ψ - g T' T'' ψ) = z.1 T T' T'' φ ψ
    have hZb : L.d0 T'' (z.1 T T' T'' φ ψ) =
        z.2.1 T T'' (φ ≫ ψ) - L.M1.map ψ (z.2.1 T T' φ) - z.2.1 T' T'' ψ := by
      rw [Zb T T' T'' φ ψ]; abel
    have hd : L.d0 T'' (z.1 T T' T'' φ ψ - (L.M0.map ψ (f₂ T T' φ - g T T' φ) -
        (f₂ T T'' (φ ≫ ψ) - g T T'' (φ ≫ ψ)) + (f₂ T' T'' ψ - g T' T'' ψ))) = 0 := by
      simp only [map_sub, map_add (f := _), L.diffZero_natural, hf₂, hg, hα, hZb, L.M1.map_comp, map_zero]
      abel
    have ha : a0 T'' (z.1 T T' T'' φ ψ - (L.M0.map ψ (f₂ T T' φ - g T T' φ) -
        (f₂ T T'' (φ ≫ ψ) - g T T'' (φ ≫ ψ)) + (f₂ T' T'' ψ - g T' T'' ψ))) = 0 := by
      simp only [map_sub, map_add (f := _), compDegreeZero_natural, hf₂', ← E0, hf, K.M0.map_comp]
      abel
    exact (sub_eq_zero.mp ((hq T'').inj0 _ hd ha)).symm
  · change Ω T' - L.M1.map φ (Ω T) - L.d0 T' (f₂ T T' φ - g T T' φ) = z.2.1 T T' φ
    rw [map_sub, hf₂, hg, hα]; abel
  · change L.d1 T (Ω T) = z.2.2 T
    rw [hΩ, map_add (f := _), hω₁, hω₂, add_zero]

theorem vertical_h2_injective : VertHas.{a, b} (fun m ↦ Function.Injective m.h2) := by
  intro C _ C' _ K K' m hq
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hx' : (QuotientAddGroup.mk (m.vert.z2 z) : K'.H2) = 0 := hx
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hx' ⊢
  obtain ⟨c', hc'⟩ := hx'
  exact cocycle_two_isCoboundary_of_objectwiseQuasiIso (L := K.res m.G) (K := K') m.a0 m.a1 m.a2 m.compDegreeZero_natural m.compDegreeOne_natural
    m.comp_commutes_diffZero m.comp_commutes_diffOne hq z.1 z.2 c'
    (fun T T' T'' φ ψ ↦ congrArg (fun c ↦ c.1 T T' T'' φ ψ) hc')
    (fun T T' φ ↦ congrArg (fun c ↦ c.2.1 T T' φ) hc')
    (fun T ↦ congrArg (fun c ↦ c.2.2 T) hc')

theorem vertical_h2_injective_universes :
    VertHas.{1,1} (fun m ↦ Function.Injective m.h2) ∧ VertHas.{1,0} (fun m ↦ Function.Injective m.h2) ∧
      VertHas.{0,0} (fun m ↦ Function.Injective m.h2) :=
  ⟨vertical_h2_injective, vertical_h2_injective, vertical_h2_injective⟩

end GlobalTheory.CxCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesL2Space
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped ENNReal NNReal

namespace GlobalTheory.KSp

theorem weil_representation_preserves_L2 : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → ∀ (μ' : Measure (Matrix α ν E)) [μ'.IsAddHaarMeasure] (g : UG c (stdJ ν E)) (φ : SB (Matrix α ν E)), ∫⁻ x, ‖(ω g φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' = ∫⁻ x, ‖(φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres _ _ μ _ κ ω hKW μ' _ g φ
  obtain ⟨hfd, htr, hinv, ht2, hc, hn, htrc, hmat⟩ := _root_.GlobalTheory.quadExt_topology F E c δ hE
  obtain ⟨hmt, hgood⟩ := hmat α ν
  haveI := hfd
  haveI := hmt
  haveI := hgood.grp
  haveI := hgood.t2
  haveI := hgood.lc
  haveI := hgood.sc
  let N : SB (Matrix α ν E) → ℝ≥0∞ := fun f => ∫⁻ x, ‖(f : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ
  let U : Subgroup (UG c (stdJ ν E)) :=
    { carrier := {g | ∀ φ, N (ω g φ) = N φ}
      one_mem' := by intro φ; simp
      mul_mem' := by
        intro g h hg hh φ
        show N (ω (g * h) φ) = N φ
        rw [map_mul, Module.End.mul_apply, hg, hh]
      inv_mem' := by
        intro g hg φ
        have := hg (ω g⁻¹ φ)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
        exact this.symm }
  have hsieg : sieg c ν ≤ U := by
    intro p hp φ
    show N (ω p φ) = N φ
    simp only [N]
    rw [hKW.par p hp φ]
    exact GlobalTheory.T.lintegral_sq_siegelParabolicOperator_eq F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ p hp φ
  obtain ⟨β, hβ, hβs, hβn, -, -⟩ := _root_.GlobalTheory.KSp.pr_alg F E c δ hE α ν Q hQ
  have hpair : IsPair (fun x y : Matrix α ν E => ψ (pr c Q x y)) := by
    have := _root_.GlobalTheory.KSp.isPair_addChar_form F (Matrix α ν E) ψ hψ hψ1 hψne β hβs hβn
    simpa only [hβ] using this
  obtain ⟨C, hC, hfi⟩ := GlobalTheory.T.bicharacterFourierTransform_twice_eq_pos_smul_reflect (Matrix α ν E) hgood μ _ hpair
  have hpl := _root_.GlobalTheory.KSp.Planch.lintegral_four_sq (Matrix α ν E) hgood μ _ hpair C hC hfi
  have hw : ∀ φ : SB (Matrix α ν E), N (ω (weyl c ν) φ) = (‖κ‖ₑ ^ 2 * ENNReal.ofReal C) * N φ := by
    intro φ
    simp only [N]
    rw [hKW.wey φ]
    simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]
    rw [lintegral_const_mul' _ _ (by simp), fou, hpl _ φ.2, mul_assoc]
  have hww : weyl c ν * weyl c ν ∈ sieg c ν := by
    rw [mem_sieg]
    show ((stdJ ν E) * (stdJ ν E)).toBlocks₂₁ = 0
    rw [stdJ_mul_stdJ]
    ext i j
    simp [toBlocks₂₁]
  obtain ⟨L, hLc, hLo, -⟩ := hgood.large ∅ isCompact_empty
  have hmem : (L : Set (Matrix α ν E)).indicator (1 : Matrix α ν E → ℂ) ∈ SB (Matrix α ν E) := by
    refine ⟨?_, ?_⟩
    · have hcl : IsClopen (L : Set (Matrix α ν E)) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
      exact (LocallyConstant.charFn ℂ hcl).isLocallyConstant
    · exact HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  set φ₀ : SB (Matrix α ν E) := ⟨_, hmem⟩ with hφ₀
  have hN0 : N φ₀ = μ L := by
    simp only [N, hφ₀]
    have e : (fun x => ‖(L : Set (Matrix α ν E)).indicator (1 : Matrix α ν E → ℂ) x‖ₑ ^ 2) =
        (L : Set (Matrix α ν E)).indicator 1 := by
      funext x
      by_cases hx : x ∈ (L : Set (Matrix α ν E)) <;> simp [hx]
    rw [e, lintegral_indicator_one hLo.measurableSet]
  have hpos : μ L ≠ 0 := (hLo.measure_pos μ ⟨0, L.zero_mem⟩).ne'
  have hfin : μ L ≠ ∞ := hLc.measure_lt_top.ne
  set k : ℝ≥0∞ := ‖κ‖ₑ ^ 2 * ENNReal.ofReal C with hk
  have hkk : k * k = 1 := by
    have h1 : N (ω (weyl c ν * weyl c ν) φ₀) = N φ₀ := hsieg hww φ₀
    rw [map_mul, Module.End.mul_apply, hw, hw, ← mul_assoc, hN0] at h1
    have h2 := congrArg (· / μ L) h1
    simpa [ENNReal.mul_div_cancel_right hpos hfin, ENNReal.div_self hpos hfin] using h2
  have hk1 : k = 1 := by
    rcases lt_trichotomy k 1 with h | h | h
    · have : k * k ≤ k * 1 := by gcongr
      rw [hkk, mul_one] at this
      exact absurd this (not_le.mpr h)
    · exact h
    · have : 1 * k ≤ k * k := by gcongr
      rw [hkk, one_mul] at this
      exact absurd this (not_le.mpr h)
  have hwU : weyl c ν ∈ U := by
    intro φ
    show N (ω (weyl c ν) φ) = N φ
    rw [hw, hk1, one_mul]
  have htop : U = ⊤ := _root_.GlobalTheory.KSp.sieg_weyl_generate F E c δ hE ν U hsieg hwU
  have hgU : g ∈ U := htop ▸ Subgroup.mem_top g
  have hμ' : μ' = Measure.addHaarScalarFactor μ' μ • μ := Measure.isAddLeftInvariant_eq_smul μ' μ
  rw [hμ', lintegral_smul_measure, lintegral_smul_measure]
  exact congrArg _ (hgU φ)
end GlobalTheory.KSp
end

