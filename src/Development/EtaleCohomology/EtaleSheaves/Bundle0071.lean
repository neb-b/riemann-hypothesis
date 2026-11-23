module

public import Development.EtaleCohomology.EtaleSheaves.CokernelKilling.KillCokOf
public import Development.EtaleCohomology.EtaleSheaves.Bundle0061
public import Development.EtaleCohomology.EtaleSheaves.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOfIsClosedOfFiniteInterClosedPoints
public import Development.EtaleCohomology.EtaleSheaves.Bundle0048
public import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling.LeafKill2Of
public import Development.EtaleCohomology.EtaleSheaves.Bundle0057
public import Development.EtaleCohomology.EtaleSheaves.Bundle0066

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.PointwisePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.PointwisePf

def PushColim : Prop := ∀ {D Y' O : CommRingCat.{0}} (φ' : D ⟶ Y') (o : D ⟶ O) {J : Type} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ CommRingCat.{0}) (t : (Functor.const J).obj D ⟶ F) (s : F ⟶ (Functor.const J).obj O),
  IsColimit (Cocone.mk O s) → (∀ j, t.app j ≫ s.app j = o) →
  ∃ (G : J ⥤ CommRingCat.{0}) (c : Cocone G) (_ : IsColimit c) (u : ∀ j, Y' ⟶ G.obj j) (ψ : ∀ j, F.obj j ⟶ G.obj j)
    (u'' : Y' ⟶ c.pt) (φ'' : O ⟶ c.pt),
    (∀ j, IsPushout φ' (t.app j) (u j) (ψ j)) ∧ (∀ {j k : J} (f : j ⟶ k), u j ≫ G.map f = u k) ∧
    (∀ {j k : J} (f : j ⟶ k), ψ j ≫ G.map f = F.map f ≫ ψ k) ∧ (∀ j, u j ≫ c.ι.app j = u'') ∧
    (∀ j, ψ j ≫ c.ι.app j = s.app j ≫ φ'') ∧ IsPushout φ' o u'' φ''

theorem pc (q : ℕ) (i m : ℤ) {X Y Z : CommRingCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (v : H (ZMod q) (sch.obj (Spec X)) (tw q i) m) :
    pull _ (sch.map (Spec.map g)) (tw q i) m (pull _ (sch.map (Spec.map f)) (tw q i) m v) =
      pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) m v := by
  rw [Spec.map_comp, Functor.map_comp, pull_comp]

theorem unit_of {A B : CommRingCat.{0}} (h : A ⟶ B) (q : ℕ) (hq : IsUnit (q : A)) : IsUnit (q : B) := by
  have := hq.map h.hom; simpa using this

theorem Pointwise_of_pushColim (hPC : PushColim) : LateralTheory.E.KillCokPf.Pointwise := by
  intro hB1 q _ i A Y φ hq D d O o hIE hBC Y' w φ' hpo m y Q hQ
  obtain ⟨J, _, _, F, t, s, hs, ht⟩ := hIE
  have ho : ∀ j, t.app j ≫ s.app j = o := fun j => (ht j).2
  obtain ⟨G, c, hc, u, ψ, u'', φ'', hpj, hu, hψ, hcu, hcψ, hpo''⟩ := hPC φ' o F t s hs ho
  have hRE : RE q i φ'' := hBC _ (w ≫ u'') φ'' (hpo.paste_vert hpo'')
  obtain ⟨z, hz⟩ := (hRE m).2 (pull _ (sch.map (Spec.map u'')) (tw q i) m y)
  obtain ⟨j, zj, hzj⟩ := (hB1 q F (Cocone.mk O s) hs m i).1 z (unit_of (d ≫ o) q hq)
  change pull _ (sch.map (Spec.map (s.app j))) (tw q i) m zj = z at hzj
  let x : H (ZMod q) (sch.obj (Spec (G.obj j))) (tw q i) m :=
    pull _ (sch.map (Spec.map (u j))) (tw q i) m y - pull _ (sch.map (Spec.map (ψ j))) (tw q i) m zj
  have hx0 : pull _ (sch.map (Spec.map (c.ι.app j))) (tw q i) m x = 0 := by
    simp only [x, map_sub, pc, hcu, hcψ, ← hz, ← hzj]
    exact sub_self _
  obtain ⟨k, f, hk⟩ := (hB1 q G c hc m i).2 j x (unit_of (d ≫ t.app j ≫ ψ j) q hq) hx0
  change pull _ (sch.map (Spec.map (G.map f))) (tw q i) m x = 0 at hk
  refine ⟨F.obj k, t.app k, Q.comap (s.app k).hom, (ht k).1, Ideal.comap_isPrime _ _, ?_, G.obj k, u k, ψ k, hpj k,
    pull _ (sch.map (Spec.map (F.map f))) (tw q i) m zj, ?_⟩
  · rw [Ideal.comap_comap, ← ho k]; rfl
  · simp only [x, map_sub, pc, hu, hψ, sub_eq_zero] at hk
    rw [pc, hk]

@[simps]
def dgm {D : CommRingCat.{0}} {J : Type} [SmallCategory J] (F : J ⥤ CommRingCat.{0}) (t : (Functor.const J).obj D ⟶ F) :
    J ⥤ Under D where
  obj j := Under.mk (t.app j)
  map {j k} f := Under.homMk (F.map f) (by simpa using (t.naturality f).symm)
  map_id j := by ext; simp
  map_comp f g := by ext; simp

@[simps]
def cone {D O : CommRingCat.{0}} (o : D ⟶ O) {J : Type} [SmallCategory J] (F : J ⥤ CommRingCat.{0})
    (t : (Functor.const J).obj D ⟶ F) (s : F ⟶ (Functor.const J).obj O) (ho : ∀ j, t.app j ≫ s.app j = o) :
    Cocone (dgm F t) where
  pt := Under.mk o
  ι := { app j := Under.homMk (s.app j) (by exact ho j)
         naturality j k f := by ext1; exact (s.naturality f).trans (Category.comp_id _) }

theorem pushColim : PushColim := by
  intro D Y' O φ' o J _ _ F t s hs ho
  have : ReflectsColimitsOfShape J (Under.forget D) := reflectsColimitsOfShape_of_reflectsIsomorphisms
  have : (Under.pushout φ').IsLeftAdjoint := ⟨_, ⟨Under.mapPushoutAdj φ'⟩⟩
  have h1 : IsColimit ((Under.forget D).mapCocone (cone o F t s ho)) :=
    IsColimit.ofIsoColimit hs (Cocone.ext (Iso.refl _) (by intro j; exact Category.comp_id _))
  have hK : IsColimit (cone o F t s ho) := isColimitOfReflects (Under.forget D) h1
  have hP := isColimitOfPreserves (Under.pushout φ') hK
  have hc := isColimitOfPreserves (Under.forget Y') hP
  refine ⟨_, _, hc, fun j => pushout.inr (t.app j) φ', fun j => pushout.inl (t.app j) φ', pushout.inr o φ', pushout.inl o φ',
    fun j => (IsPushout.of_hasPushout (t.app j) φ').flip, ?_, ?_, ?_, ?_, (IsPushout.of_hasPushout o φ').flip⟩
  · intro j k f; simp [Under.pushout]; exact pushout.inr_desc _ _ _
  · intro j k f; simp [Under.pushout]; exact pushout.inl_desc _ _ _
  · intro j; simp [Under.pushout]; exact pushout.inr_desc _ _ _
  · intro j; simp [Under.pushout]; exact pushout.inl_desc _ _ _

end LateralTheory.E.PointwisePf

namespace LateralTheory.E.PointwisePf

end LateralTheory.E.PointwisePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ProjectiveLineTwoAffineChartsPolynomialGenerated
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.GeometricData

namespace LateralTheory.E.ProjectiveLineCharts₂

def ProjectiveLineTwoAffineChartsPolynomialGenerated : Prop :=
  ∃ (U V : P1.Opens) (s : Γ(P1, U)) (s' : Γ(P1, V)), IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ ∧
    P1.basicOpen s = U ⊓ V ∧ P1.basicOpen s' = U ⊓ V ∧
    P1.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s *
      P1.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s' = 1 ∧
    Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(P1, U)) s) ∧
    Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(P1, V)) s')

def ChartBC : Prop := ∀ (A : Type) [CommRing A] {L : Scheme.{0}} (l : L ⟶ Spec (CommRingCat.of A)) (f : L ⟶ P1),
  IsPullback f l (terminal.from P1) (terminal.from _) → ∀ (W : P1.Opens) (x : Γ(P1, W)), IsAffineOpen W →
  Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(P1, W)) x) →
  IsAffineOpen (f ⁻¹ᵁ W) ∧ Function.Surjective (Polynomial.eval₂RingHom (rA l (f ⁻¹ᵁ W)) (f.app W x))

theorem rA_comp {A : Type} [CommRing A] {Z L : Scheme.{0}} (u : Z ⟶ L) (l : L ⟶ Spec (CommRingCat.of A))
    (W : L.Opens) : rA (u ≫ l) (u ⁻¹ᵁ W) = (u.app W).hom.comp (rA l W) := by
  simp only [rA]
  rw [← Scheme.Hom.appLE_comp_appLE u l ⊤ W (u ⁻¹ᵁ W) le_top le_rfl, u.appLE_eq_app]
  rfl

theorem res_app {X Y : Scheme.{0}} (g : X ⟶ Y) {W W' : Y.Opens} (h : W' ≤ W) (x : Γ(Y, W)) :
    X.presheaf.map (homOfLE (g.preimage_mono h)).op (g.app W x) = g.app W' (Y.presheaf.map (homOfLE h).op x) := by
  have := congrArg (fun φ => φ.hom x) (g.naturality (homOfLE h).op)
  exact this.symm

theorem transport {X Y : Scheme.{0}} (g : X ⟶ Y) {U V : Y.Opens} (s : Γ(Y, U)) (s' : Γ(Y, V))
    (h1 : U ⊔ V = ⊤) (h2 : Y.basicOpen s = U ⊓ V) (h3 : Y.basicOpen s' = U ⊓ V)
    (h4 : Y.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s *
      Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s' = 1) :
    g ⁻¹ᵁ U ⊔ g ⁻¹ᵁ V = ⊤ ∧ X.basicOpen (g.app U s) = g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ∧
    X.basicOpen (g.app V s') = g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ∧
    X.presheaf.map (homOfLE (inf_le_left : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U)).op (g.app U s) *
      X.presheaf.map (homOfLE (inf_le_right : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ V)).op (g.app V s') = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Scheme.Hom.preimage_sup, h1]; rfl
  · rw [← Scheme.preimage_basicOpen, h2]; rfl
  · rw [← Scheme.preimage_basicOpen, h3]; rfl
  · erw [res_app g inf_le_left s, res_app g inf_le_right s', ← map_mul, h4]
    exact map_one _

theorem LineOpens_of (hP : ProjectiveLineTwoAffineChartsPolynomialGenerated) (hB : ChartBC) : LineOpens := by
  intro A _ _ Z p hIL hZ
  obtain ⟨L, u, l, hu, ⟨_, f, hf⟩, rfl⟩ := hIL
  obtain ⟨U0, V0, x, y, hU0, hV0, h1, h2, h3, h4, hsx, hsy⟩ := hP
  obtain ⟨hU1, hsU⟩ := hB A l f hf U0 x hU0 hsx
  obtain ⟨hV1, hsV⟩ := hB A l f hf V0 y hV0 hsy
  obtain ⟨k1, k2, k3, k4⟩ := transport f x y h1 h2 h3 h4
  obtain ⟨m1, m2, m3, m4⟩ := transport u _ _ k1 k2 k3 k4
  have hUa : IsAffineOpen (u ⁻¹ᵁ (f ⁻¹ᵁ U0)) := hU1.preimage u
  have hVa : IsAffineOpen (u ⁻¹ᵁ (f ⁻¹ᵁ V0)) := hV1.preimage u
  have hint : ∀ (W : L.Opens) (z : Γ(L, W)), IsAffineOpen W →
      Function.Surjective (Polynomial.eval₂RingHom (rA l W) z) →
      (Polynomial.eval₂RingHom (rA (u ≫ l) (u ⁻¹ᵁ W)) (u.app W z)).IsIntegral := by
    intro W z hW hs
    have he : Polynomial.eval₂RingHom (rA (u ≫ l) (u ⁻¹ᵁ W)) (u.app W z) =
        (u.app W).hom.comp (Polynomial.eval₂RingHom (rA l W) z) := by
      apply Polynomial.ringHom_ext
      · intro a; simp [rA_comp]
      · simp
    rw [he]
    exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ hs) (u.isIntegral_app W hW)
  by_cases hne : ((u ⁻¹ᵁ (f ⁻¹ᵁ U0) ⊓ u ⁻¹ᵁ (f ⁻¹ᵁ V0) : Z.Opens) : Set Z).Nonempty
  · exact Or.inr ⟨_, _, _, _, hUa, hVa, m1, m2, m3, hne, m4, hint _ _ hU1 hsU, hint _ _ hV1 hsV⟩
  · left
    have : IsIntegral Z := hZ.1
    have hUV : ¬ (((u ⁻¹ᵁ (f ⁻¹ᵁ U0) : Z.Opens) : Set Z).Nonempty ∧
        ((u ⁻¹ᵁ (f ⁻¹ᵁ V0) : Z.Opens) : Set Z).Nonempty) := by
      rintro ⟨a, b⟩
      exact hne (nonempty_preirreducible_inter (u ⁻¹ᵁ (f ⁻¹ᵁ U0)).isOpen (u ⁻¹ᵁ (f ⁻¹ᵁ V0)).isOpen a b)
    rcases not_and_or.mp hUV with h | h
    · have : u ⁻¹ᵁ (f ⁻¹ᵁ V0) = ⊤ := by
        rw [eq_top_iff]; intro z _
        have hz : z ∈ u ⁻¹ᵁ (f ⁻¹ᵁ U0) ⊔ u ⁻¹ᵁ (f ⁻¹ᵁ V0) := m1 ▸ trivial
        rcases (TopologicalSpace.Opens.mem_sup.mp hz) with hz | hz
        · exact absurd ⟨z, hz⟩ h
        · exact hz
      exact this ▸ hVa
    · have : u ⁻¹ᵁ (f ⁻¹ᵁ U0) = ⊤ := by
        rw [eq_top_iff]; intro z _
        have hz : z ∈ u ⁻¹ᵁ (f ⁻¹ᵁ U0) ⊔ u ⁻¹ᵁ (f ⁻¹ᵁ V0) := m1 ▸ trivial
        rcases (TopologicalSpace.Opens.mem_sup.mp hz) with hz | hz
        · exact hz
        · exact absurd ⟨z, hz⟩ h
      exact this ▸ hUa

end LateralTheory.E.ProjectiveLineCharts₂
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PushGluePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.KillCokPf.Asm
open scoped TensorProduct

namespace LateralTheory.E.PushGluePf

abbrev pS (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    H R (sch.obj (Spec A)) F n →+ H R (sch.obj (Spec B)) F n :=
  pull R (sch.map (Spec.map f)) F n

theorem pS_comp (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C)
    (x : H R (sch.obj (Spec A)) F n) : pS R F n (f ≫ g) x = pS R F n g (pS R F n f x) := by
  simp only [pS]; rw [Spec.map_comp, Functor.map_comp, pull_comp]

abbrev ev {ι : Type} (Y : ι → CommRingCat.{0}) (j : ι) : CommRingCat.of (∀ k, Y k) ⟶ Y j :=
  CommRingCat.ofHom (Pi.evalRingHom (fun k => Y k) j)

theorem pull_iso_bij (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {E E' : Spc} (g : E ⟶ E') [IsIso g] :
    Function.Bijective (pull R g F n) := by
  have h1 : ∀ x, pull R (inv g) F n (pull R g F n x) = x := fun x => by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  have h2 : ∀ x, pull R g F n (pull R (inv g) F n x) = x := fun x => by
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem pi_bij (hC : Coprod) (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {ι : Type} [Finite ι]
    (Y : ι → CommRingCat.{0}) :
    Function.Bijective fun (x : H R (sch.obj (Spec (CommRingCat.of (∀ k, Y k)))) F n) (j : ι) => pS R F n (ev Y j) x := by
  have h : (fun (x : H R (sch.obj (Spec (CommRingCat.of (∀ k, Y k)))) F n) (j : ι) => pS R F n (ev Y j) x) =
      (fun (x : H R (sch.obj (∐ fun k => Spec (Y k))) F n) (j : ι) =>
        pull R (sch.map (Sigma.ι (fun k => Spec (Y k)) j)) F n x) ∘ pull R (sch.map (sigmaSpec Y)) F n := by
    funext x j
    simp only [Function.comp_apply, pS, ev]
    rw [← pull_comp, ← Functor.map_comp, ι_sigmaSpec]
  rw [h]
  exact (hC R F (fun k => Spec (Y k)) n).comp (pull_iso_bij R F n _)

theorem pushout_pi {D Y' : CommRingCat.{0}} (φ' : D ⟶ Y') {ι : Type} [Fintype ι] (D₁ : ι → CommRingCat.{0})
    (e : ∀ k, D ⟶ D₁ k) (Y₁ : ι → CommRingCat.{0}) (u : ∀ k, Y' ⟶ Y₁ k) (φ₁ : ∀ k, D₁ k ⟶ Y₁ k)
    (hpo : ∀ k, IsPushout φ' (e k) (u k) (φ₁ k)) :
    IsPushout φ' (piMap D₁ e) (CommRingCat.ofHom (Pi.ringHom fun k => (u k).hom))
      (CommRingCat.ofHom (Pi.ringHom fun k => (φ₁ k).hom.comp (Pi.evalRingHom (fun k => D₁ k) k))) := by
  classical
  letI : Algebra D Y' := φ'.hom.toAlgebra
  letI : ∀ k, Algebra D (D₁ k) := fun k => (e k).hom.toAlgebra
  have hT : IsPushout φ' (piMap D₁ e) _ _ := CommRingCat.isPushout_tensorProduct D Y' (∀ k, D₁ k)
  have hTk : ∀ k, IsPushout φ' (e k) _ _ := fun k => CommRingCat.isPushout_tensorProduct D Y' (D₁ k)
  let isk : ∀ k, CommRingCat.of (Y' ⊗[D] D₁ k) ≅ Y₁ k := fun k => IsPushout.isoIsPushout _ _ (hTk k) (hpo k)
  have hl : ∀ k (y : Y'), (isk k).hom (y ⊗ₜ 1) = u k y := fun k y => by
    have := IsPushout.inl_isoIsPushout_hom _ _ (hTk k) (hpo k)
    exact congrArg (fun f => f.hom y) this
  have hr : ∀ k (d : D₁ k), (isk k).hom (1 ⊗ₜ d) = φ₁ k d := fun k d => by
    have := IsPushout.inr_isoIsPushout_hom _ _ (hTk k) (hpo k)
    exact congrArg (fun f => f.hom d) this
  let e₄ : CommRingCat.of (Y' ⊗[D] (∀ k, D₁ k)) ≅ CommRingCat.of (∀ k, Y₁ k) :=
    ((Algebra.TensorProduct.piRight D D Y' (fun k => D₁ k)).toRingEquiv.trans
      (RingEquiv.piCongrRight fun k => (isk k).commRingCatIsoToRingEquiv)).toCommRingCatIso
  refine hT.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e₄ (by simp) (by simp) ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun y => funext fun k => ?_)
    have h4 : e₄.hom (y ⊗ₜ (1 : ∀ k, D₁ k)) k = (isk k).hom (y ⊗ₜ 1) := by
      simp [e₄, Algebra.TensorProduct.piRight_tmul]; rfl
    exact h4.trans (hl k y)
  · refine CommRingCat.hom_ext (RingHom.ext fun d => funext fun k => ?_)
    have h4 : e₄.hom ((1 : Y') ⊗ₜ d) k = (isk k).hom (1 ⊗ₜ d k) := by
      simp [e₄, Algebra.TensorProduct.piRight_tmul]; rfl
    exact h4.trans (hr k (d k))

theorem PushGlue_of (hC : Coprod) : LateralTheory.E.KillCokPf.Glue.PushGlue := by
  intro _ q _ i D Y' φ' m y ι _ D₁ e _ hk
  classical
  choose Y₁ u φ₁ hpo hz using hk
  choose z hz using hz
  obtain ⟨z₀, hz₀⟩ := (pi_bij hC (ZMod q) (tw q i) m D₁).2 z
  have hz₀' : ∀ j, pS _ (tw q i) m (ev D₁ j) z₀ = z j := fun j => congrFun hz₀ j
  let u'' : Y' ⟶ CommRingCat.of (∀ k, Y₁ k) := CommRingCat.ofHom (Pi.ringHom fun k => (u k).hom)
  let φ'' : CommRingCat.of (∀ k, D₁ k) ⟶ CommRingCat.of (∀ k, Y₁ k) :=
    CommRingCat.ofHom (Pi.ringHom fun k => (φ₁ k).hom.comp (Pi.evalRingHom (fun k => D₁ k) k))
  refine ⟨CommRingCat.of (∀ k, Y₁ k), u'', φ'', ?_, z₀, ?_⟩
  · exact pushout_pi φ' D₁ e Y₁ u φ₁ hpo
  · apply (pi_bij hC (ZMod q) (tw q i) m Y₁).1
    funext j
    have e1 : φ'' ≫ ev Y₁ j = ev D₁ j ≫ φ₁ j := rfl
    have e2 : u'' ≫ ev Y₁ j = u j := rfl
    show pS _ (tw q i) m (ev Y₁ j) (pS _ (tw q i) m φ'' z₀) = pS _ (tw q i) m (ev Y₁ j) (pS _ (tw q i) m u'' y)
    rw [← pS_comp, ← pS_comp, e1, e2, pS_comp, hz₀']
    exact hz j

end LateralTheory.E.PushGluePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.QuotientFieldNonconstantLift
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.QuotientFieldNonconstantLift

def LeafCurveSmall : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  (Set.univ : Set C).Infinite ∧ ∀ Z : Set C, IsClosed Z → Z.Infinite → Z = Set.univ

def LeafLiftNonconst : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    ∀ (he : e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))), genericPoint X ∈ Set.range e →
    ∀ y : C0, ∃ a : C0, pullback.lift c0 e he.symm a ≠ pullback.lift c0 e he.symm y

theorem lqf_of_nonconst (hC : LeafCurveSmall) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {C Y : Scheme.{0}}
    (c : C ⟶ Sp Ω) (hc : IsCurve c) (g : C ⟶ Y) [LocallyOfFiniteType g] [UniversallyClosed g]
    (hn : ∀ y, ∃ a, g a ≠ g y) : LocallyQuasiFinite g := by
  obtain ⟨_, _, _⟩ := id hc
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace c
  refine GlobalTheory.locallyQuasiFinite_of_finite_fibres_closedPoints g fun y hy => ?_
  have hcl : IsClosed ({g y} : Set Y) := by
    have := g.isClosedMap _ hy
    simpa using this
  by_contra hinf
  have := (hC Ω c hc).2 _ (hcl.preimage g.continuous) hinf
  obtain ⟨a, ha⟩ := hn y
  have : a ∈ g ⁻¹' {g y} := this ▸ Set.mem_univ a
  exact ha this

theorem nonconst_of_surj (hC : LeafCurveSmall) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {C0 C1 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω) (hc : IsCurve c0) (g : C1 ⟶ C0) (hg : Surjective g) (y : C1) : ∃ a, g a ≠ g y := by
  obtain ⟨b, hb⟩ := ((hC Ω c0 hc).1.sdiff (Set.finite_singleton (g y))).nonempty
  obtain ⟨a, rfl⟩ := hg.surj b
  exact ⟨a, by simpa using hb.2⟩

theorem lqf_gamma (hC : LeafCurveSmall) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {C0 C1 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω) (hc : IsCurve c0) (g : C1 ⟶ C0) (hc1 : IsCurve (g ≫ c0)) (hg : Surjective g) :
    LocallyQuasiFinite g := by
  obtain ⟨_, _, _⟩ := id hc
  obtain ⟨_, _, _⟩ := id hc1
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g c0
  have : UniversallyClosed g := UniversallyClosed.of_comp_of_isSeparated g c0
  exact lqf_of_nonconst hC (g ≫ c0) hc1 g (nonconst_of_surj hC c0 hc g hg)

theorem LeafQFOmega_of (hC : LeafCurveSmall) (hL : LeafLiftNonconst) :
    LateralTheory.E.QuasiFiniteDescent.LeafQFOmega := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hgen C1 C2 γ1 γ2 h1 h2 s1 s2
  refine ⟨?_, lqf_gamma hC c0 hc0 γ1 h1 s1, lqf_gamma hC (γ1 ≫ c0) h1 γ2 h2 s2⟩
  obtain ⟨_, _, _⟩ := id hc0
  set g := pullback.lift c0 e he.symm with hgdef
  have hfst : g ≫ pullback.fst _ _ = c0 := pullback.lift_fst _ _ _
  have : LocallyOfFiniteType (g ≫ pullback.fst _ _) := by rw [hfst]; infer_instance
  have : UniversallyClosed (g ≫ pullback.fst _ _) := by rw [hfst]; infer_instance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (pullback.fst _ _)
  have : UniversallyClosed g := UniversallyClosed.of_comp_of_isSeparated g (pullback.fst _ _)
  exact lqf_of_nonconst hC c0 hc0 g (hL k p Ω hdim c0 e hc0 he hgen)

end LateralTheory.E.QuotientFieldNonconstantLift
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.RTEqZeroOfPtA
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafKill1V2Cut
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem goal_of' (hN : LateralTheory.E.SecondDegreeKilling.Nbhd.LeafKillNbhd) (hW : LateralTheory.E.SecondDegreeKilling.LeafPtW)
    (hV : LateralTheory.E.SecondDegreeKilling.LeafPtV) : LateralTheory.E.LeafDegCut.LeafKill1 := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s ι _ V hV' p g1 g2 hp hp1 hp2 hSHV U y
  refine LateralTheory.E.SecondDegreeKilling.Nbhd.killPt_of hN hH q k hq i s ι (g2 ≫ g1 ≫ p) hp2 U 1 (gY q i (g1 ≫ p) g2 ι U 1 y) ?_
  intro A _ t hA
  by_cases h : Set.range (t ≫ U.hom : Sp A ⟶ B) ⊆ (V : Set B)
  · exact hV hH q k hq i s ι V hV' (g1 ≫ p) g2 hp1 hp2 U A t hA h 1 (hSHV A (t ≫ U.hom) hA h).2.2.1 y
  · have := hW hH q k hq i s ι V hV' (g2 ≫ g1 ≫ p) hp2 A (t ≫ U.hom) hA h 1
    exact Subsingleton.elim _ _

end LateralTheory.E.LeafKill1V2Cut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StalkVanishing
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.StalkVanishing
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem goal_of (hN : LateralTheory.E.SecondDegreeKilling.Nbhd.LeafKillNbhd) : LateralTheory.E.LeafVan0Pf.LeafVanStalk := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp U m hsub y
  refine LateralTheory.E.SecondDegreeKilling.Nbhd.killPt_of hN hH q k hq i toK ι p hp U m y ?_
  intro A _ t hA
  have := hsub A t hA
  exact Subsingleton.elim _ _

end LateralTheory.E.StalkVanishing
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SysFMPfAlg
section
namespace LateralTheory.E.SysFMPfAlg

open LateralTheory.E.BuildCut

theorem prime_of_filter {W : Type} [CommRing W] (hW : ProdACF W) (F : Set W) (hF : ∀ e ∈ F, IsIdempotentElem e)
    (h0 : (0 : W) ∉ F) (hu : ∀ e, IsIdempotentElem e → e ∈ F ∨ 1 - e ∈ F) (hm : ∀ e ∈ F, ∀ f ∈ F, e * f ∈ F) :
    ∃ q : PrimeSpectrum W, ∀ e, IsIdempotentElem e → (e ∉ q.asIdeal ↔ e ∈ F) := by
  have h1 : (1 : W) ∈ F := by
    rcases hu 0 IsIdempotentElem.zero with h | h
    · exact absurd h h0
    · simpa using h
  let I : Ideal W :=
    { carrier := {a | ∃ f ∈ F, a * f = 0}
      add_mem' := by
        rintro a b ⟨f, hf, ha⟩ ⟨g, hg, hb⟩
        exact ⟨f * g, hm f hf g hg, by linear_combination g * ha + f * hb⟩
      zero_mem' := ⟨1, h1, by simp⟩
      smul_mem' := by
        rintro c a ⟨f, hf, ha⟩
        exact ⟨f, hf, by simp only [smul_eq_mul]; linear_combination c * ha⟩ }
  have key : ∀ e, IsIdempotentElem e → (e ∈ I ↔ e ∉ F) := by
    intro e he
    constructor
    · rintro ⟨f, hf, hef⟩ heF
      exact h0 (hef ▸ hm e heF f hf)
    · intro heF
      rcases hu e he with h | h
      · exact absurd h heF
      · exact ⟨1 - e, h, by rw [mul_sub, mul_one, he.eq, sub_self]⟩
  have hI : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one]
      rintro ⟨f, hf, h⟩
      rw [one_mul] at h
      exact h0 (h ▸ hf)
    · intro a b hab
      obtain ⟨e, u, he, hu', rfl⟩ := hW.2 a
      obtain ⟨e', u', he', hu'', rfl⟩ := hW.2 b
      by_contra hn
      push Not at hn
      have ha : e ∈ F := by
        by_contra h
        exact hn.1 ⟨1 - e, (hu e he).resolve_left h, by
          rw [mul_assoc, mul_comm u, ← mul_assoc, mul_sub, mul_one, he.eq, sub_self, zero_mul]⟩
      have hb : e' ∈ F := by
        by_contra h
        exact hn.2 ⟨1 - e', (hu e' he').resolve_left h, by
          rw [mul_assoc, mul_comm u', ← mul_assoc, mul_sub, mul_one, he'.eq, sub_self, zero_mul]⟩
      obtain ⟨f, hf, h⟩ := hab
      have hz : e * e' * f = 0 := by
        obtain ⟨v, hv⟩ := hu'.exists_left_inv
        obtain ⟨v', hv'⟩ := hu''.exists_left_inv
        linear_combination (v * v') * h - (e * e' * f) * hv - (e * e' * f * v * u) * hv'
      exact h0 (hz ▸ hm _ (hm e ha e' hb) f hf)
  refine ⟨⟨I, hI⟩, fun e he => ?_⟩
  rw [show (⟨I, hI⟩ : PrimeSpectrum W).asIdeal = I from rfl, key e he, not_not]


open AlgebraicGeometry in
theorem isClosed_basicOpen_idem {X : Scheme.{0}} {s : Γ(X, ⊤)} (hs : IsIdempotentElem s) :
    IsClosed (X.basicOpen s : Set X) := by
  have : (X.basicOpen s : Set X)ᶜ = (X.basicOpen (1 - s) : Set X) := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe, Scheme.mem_basicOpen_top, map_sub, map_one]
    have he : IsIdempotentElem (X.presheaf.germ ⊤ x trivial s) := hs.map _
    constructor
    · intro h
      exact (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left h
    · intro h h'
      have hz : X.presheaf.germ ⊤ x trivial s * (1 - X.presheaf.germ ⊤ x trivial s) = 0 := by
        rw [mul_sub, mul_one, he.eq, sub_self]
      exact not_isUnit_zero (hz ▸ h'.mul h)
  rw [← isOpen_compl_iff, this]
  exact (X.basicOpen (1 - s)).isOpen

open AlgebraicGeometry in
theorem isClosedImmersion_basicOpen_idem {X : Scheme.{0}} {s : Γ(X, ⊤)} (hs : IsIdempotentElem s) :
    IsClosedImmersion (X.basicOpen s).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact isClosed_basicOpen_idem hs)

end LateralTheory.E.SysFMPfAlg
end

