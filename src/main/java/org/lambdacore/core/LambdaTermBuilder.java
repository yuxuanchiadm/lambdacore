package org.lambdacore.core;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

public class LambdaTermBuilder {
	public final Map<String, Set<String>> categoryMap = new HashMap<>();
	private String currentCategoryName;
	private Set<String> currentCategory;

	public final Map<String, Binding> bindingMap = new HashMap<>();
	public final List<Binding> bindingList = new ArrayList<>();

	public void beginCategory(String categoryName) {
		if (currentCategoryName != null)
			throw new IllegalStateException("Already has current category");
		Set<String> newCategory = categoryMap.get(categoryName);
		if (newCategory == null)
			categoryMap.put(categoryName, newCategory = new HashSet<>());
		currentCategoryName = categoryName;
		currentCategory = newCategory;
	}

	public void endCategory() {
		if (currentCategoryName == null)
			throw new IllegalStateException("No current category");
		currentCategoryName = null;
		currentCategory = null;
	}

	public void registerDefaultTerms() {
		beginCategory("function");
		{
			registerTerm( //
				"id", //
				"a -> a", //
				"λx.x", //
				false);
			registerTerm( //
				"const", //
				"a -> b -> a", //
				"λx.λy.x", //
				false);
			registerTerm( //
				"subst", //
				"(a -> b -> c) -> (a -> b) -> a -> c", //
				"λf.λg.λx.f x (g x)", //
				false);
			registerTerm( //
				"compose", //
				"(b -> c) -> (a -> b) -> a -> c", //
				"λf.λg.λx.f (g x)", //
				false);
			registerTerm( //
				"flip", //
				"(a -> b -> c) -> b -> a -> c", //
				"λf.λx.λy.f y x", //
				false);
			registerTerm( //
				"apply", //
				"(a -> b) -> a -> b", //
				"λf.λx.f x", //
				false);
			registerTerm( //
				"reverseApply", //
				"a -> (a -> b) -> b", //
				"λx.λf.f x", //
				false);
			registerTerm( //
				"prepose", //
				"(n : Nat) -> {t : Vect n Type} -> (b -> c) -> (foldr (->) b t) -> (foldr (->) c t)", //
				"λn.λf.λg.n (λh.λi.λx.h (λu.i u x)) (λu.f (u g)) (λu.u)", //
				false);
			registerTerm( //
				"fix", //
				"(a -> a) -> a", //
				"λf.(λx.f (x x)) (λx.f (x x))", //
				false);
		}
		endCategory();

		beginCategory("nat");
		{
			registerTerm( //
				"zero", //
				"Nat", //
				"λf.λx.x", //
				false);
			registerTerm( //
				"succ", //
				"Nat -> Nat", //
				"λn.λf.λx.f (n f x)", //
				false);

			registerTerm( //
				"plus", //
				"Nat -> Nat -> Nat", //
				"λm.λn.λf.λx.m f (n f x)", //
				false);
			registerTerm( //
				"mult", //
				"Nat -> Nat -> Nat", //
				"λm.λn.λf.m (n f)", //
				false);
			registerTerm( //
				"pow", //
				"Nat -> Nat -> Nat", //
				"λm.λn.n m", //
				false);

			registerTerm( //
				"pred", //
				"Nat -> Nat", //
				"λn.λf.λx.n (λg.λh.h (g f)) (λu.x) (λu.u)", //
				false);
		}
		endCategory();

		beginCategory("bool");
		{
			registerTerm( //
				"bool", //
				"a -> a -> Bool -> a", //
				"λt.λf.λb.b t f", //
				false);
			registerTerm( //
				"false", //
				"Bool", //
				"λt.λf.f", //
				false);
			registerTerm( //
				"true", //
				"Bool", //
				"λt.λf.t", //
				false);

			registerTerm( //
				"and", //
				"Bool -> Bool -> Bool", //
				"λp.λq.p q p", //
				false);
			registerTerm( //
				"or", //
				"Bool -> Bool -> Bool", //
				"λp.λq.p p q", //
				false);
			registerTerm( //
				"not", //
				"Bool -> Bool", //
				"λb.λt.λf.b f t", //
				false);
			registerTerm( //
				"if", //
				"Bool -> a -> a -> a", //
				"λb.λt.λf.b t f", //
				false);
		}
		endCategory();

		beginCategory("maybe");
		{
			registerTerm( //
				"maybe", //
				"b -> (a -> b) -> Maybe a -> b", //
				"λn.λj.λm.m n j", //
				false);
			registerTerm( //
				"nothing", //
				"Maybe a", //
				"λn.λj.n", //
				false);
			registerTerm( //
				"just", //
				"a -> Maybe a", //
				"λx.λn.λj.j x", //
				false);

			registerTerm( //
				"isNothing", //
				"Maybe a -> Bool", //
				"λm.m true (λx. false)", //
				false, //
				"false", "true");
			registerTerm( //
				"isJust", //
				"Maybe a -> Bool", //
				"λm.m false (λx. true)", //
				false, //
				"false", "true");

			registerTerm( //
				"fromMaybe", //
				"a -> Maybe a -> a", //
				"λx.λm.m x (λu.u)", //
				false);
		}
		endCategory();

		beginCategory("list");
		{
			registerTerm( //
				"list", //
				"b -> (a -> List a -> b) -> List a -> b", //
				"λn.λc.λl.l n c", //
				false);
			registerTerm( //
				"nil", //
				"List a", //
				"λn.λc.n", //
				false);
			registerTerm( //
				"cons", //
				"a -> List a -> List a", //
				"λh.λt.λn.λc.c h t", //
				false);

			registerTerm( //
				"append", //
				"List a -> List a -> List a", //
				"λl.λm.l m (λh.λt.cons h (append t m))", //
				true, //
				"cons");

			registerTerm( //
				"head", //
				"List a -> Maybe a", //
				"λl.l nothing (λh.λt.just h)", //
				false, //
				"nothing", "just");
			registerTerm( //
				"last", //
				"List a -> Maybe a", //
				"λl.l nothing (prepose 2 just (fix (λf.λh.λt.t h f)))", //
				false, //
				"2", "nothing", "just", "prepose", "fix");
			registerTerm( //
				"tail", //
				"List a -> Maybe (List a)", //
				"λl.l nothing (λh.λt.just t)", //
				false, //
				"nothing", "just");
			registerTerm( //
				"init", //
				"List a -> Maybe (List a)",
				"λl.l nothing (prepose 2 just (fix (λf.λh.λt.t nil (prepose 2 (cons h) f))))", //
				false, //
				"2", "nothing", "just", "prepose", "fix", "nil", "cons");

			registerTerm( //
				"null", //
				"List a -> Bool", //
				"λl.l true (λh.λt.false)", //
				false, //
				"false", "true");
			registerTerm( //
				"length", //
				"List a -> Nat", //
				"λl.l zero (λh.λt.succ (length t))", //
				true, //
				"zero", "succ");

			registerTerm( //
				"map", //
				"(a -> b) -> List a -> List b", //
				"λf.λl.l nil (λh.λt.cons (f h) (map f t))", //
				true, //
				"nil", "cons");
			registerTerm( //
				"reverse", //
				"List a -> List a", //
				"λl.(fix (λf.λm.λn.m n (λh.λt.f t (cons h n)))) l nil", //
				false, //
				"fix", "nil", "cons");

			registerTerm( //
				"foldr", //
				"(a -> b -> b) -> b -> List a -> b", //
				"λf.λx.λl.l x (λh.λt.f h (foldr f x t))", //
				true);
			registerTerm( //
				"foldl", //
				"(a -> b -> a) -> a -> List b -> a", //
				"λf.λx.λl.l x (λh.λt.foldl f (f x h) t)", //
				true);
		}
		endCategory();
	}

	public void registerTerm(String variable, String type, String term, boolean needFix, String... dependencies) {
		registerTerm(variable, type, term, needFix, Arrays.stream(dependencies).collect(Collectors.toSet()));
	}

	public void registerTerm(String variable, String type, String term, boolean needFix, Set<String> dependencies) {
		if (currentCategory == null)
			throw new IllegalStateException("No current category");
		if (bindingMap.containsKey(variable) || parseNatLiteral(variable).isPresent())
			throw new IllegalStateException("variable already registered");
		if (needFix)
			dependencies.add("fix");
		Set<String> indirectDependencies = new HashSet<>();
		for (String dependency : dependencies)
			if (bindingMap.containsKey(dependency)) {
				indirectDependencies.add(dependency);
				indirectDependencies.addAll(indirectDependencies);
			} else if (parseNatLiteral(dependency).isPresent())
				indirectDependencies.add(dependency);
			else
				throw new IllegalStateException("dependencies not satisfy");
		Binding binding = new Binding(variable, type, term, needFix, new HashSet<>(dependencies), indirectDependencies);
		currentCategory.add(variable);
		bindingMap.put(variable, binding);
		bindingList.add(binding);
	}

	public String buildTerm(String term, String... dependencies) {
		return buildTerm(term, Arrays.stream(dependencies).collect(Collectors.toSet()));
	}

	public String buildTerm(String term, Set<String> dependencies) {
		List<Binding> bindingDependencies = findBindingDependencies(dependencies);
		while (!bindingDependencies.isEmpty()) {
			Binding binding = bindingDependencies.remove(bindingDependencies.size() - 1);
			term = "(λ" + binding.getVariable() + ".(" + term + ")) (" + binding.buildTerm() + ")";
		}
		return term;
	}

	public List<Binding> findBindingDependencies(String... dependencies) {
		return findBindingDependencies(Arrays.stream(dependencies).collect(Collectors.toSet()));
	}

	public List<Binding> findBindingDependencies(Set<String> dependencies) {
		Set<String> fullDependencies = new HashSet<>(dependencies);
		for (String dependency : dependencies) {
			Binding binding;
			if ((binding = bindingMap.get(dependency)) != null) {
				fullDependencies.add(dependency);
				fullDependencies.addAll(binding.getIndirectDependencies());
			} else if (parseNatLiteral(dependency).isPresent())
				fullDependencies.add(dependency);
			else
				throw new IllegalStateException("dependencies not satisfy");
		}
		List<Binding> bindingDependenciesList = new ArrayList<>();
		for (String dependency : fullDependencies) {
			parseNatLiteral(dependency).ifPresent(lit -> bindingDependenciesList
				.add(new Binding(dependency, "Nat", buildNatLiteral(lit), false, new HashSet<>(), new HashSet<>())));
		}
		bindingDependenciesList.addAll(bindingList);
		Iterator<Binding> bindingDependenciesIterator = bindingDependenciesList.iterator();
		while (bindingDependenciesIterator.hasNext()) {
			Binding bindingDependency = bindingDependenciesIterator.next();
			if (!fullDependencies.contains(bindingDependency.getVariable()))
				bindingDependenciesIterator.remove();
		}
		return bindingDependenciesList;
	}

	public String buildNatLiteral(int lit) {
		StringBuilder builder = new StringBuilder("λf.λx.");
		for (int i = 0; i < lit; i++)
			builder.append(i == 0 ? "f " : "(f ");
		builder.append("x");
		for (int i = 0; i < lit; i++)
			builder.append(i == 0 ? "" : ")");
		return builder.toString();
	}

	public String buildBinaryNatLiteral(int lit) {
		if (lit < 0)
			throw new ArithmeticException();
		String binaryNat = (lit & (1 << 0)) != 0 ? buildNatLiteral(1) : buildNatLiteral(0);
		for (int i = 1; i < 31; i++)
			if ((lit & (1 << i)) != 0)
				binaryNat = "a ((" + buildNatLiteral(i) + ") (" + buildNatLiteral(2) + ")) (" + binaryNat + ")";
		return "(λa." + binaryNat + ") (λm.λn.λf.λx.m f (n f x))";
	}

	public Optional<Integer> parseNatLiteral(String lit) {
		try {
			return Optional.of(Integer.parseUnsignedInt(lit));
		} catch (NumberFormatException e) {
			return Optional.empty();
		}
	}

	public static class Binding {
		private final String variable;
		private final String type;
		private final String term;
		private final boolean needFix;
		private final Set<String> dependencies;
		private final Set<String> indirectDependencies;

		public Binding(String variable, String type, String term, boolean needFix, Set<String> dependencies,
			Set<String> indirectDependencies) {
			this.variable = variable;
			this.type = type;
			this.term = term;
			this.needFix = needFix;
			this.dependencies = dependencies;
			this.indirectDependencies = indirectDependencies;
		}

		public String getVariable() {
			return variable;
		}

		public String getType() {
			return type;
		}

		public String getTerm() {
			return term;
		}

		public boolean isNeedFix() {
			return needFix;
		}

		public Set<String> getDependencies() {
			return dependencies;
		}

		public Set<String> getIndirectDependencies() {
			return indirectDependencies;
		}

		public String buildTerm() {
			return needFix ? "fix (λ" + variable + ".(" + term + "))" : term;
		}
	}
}