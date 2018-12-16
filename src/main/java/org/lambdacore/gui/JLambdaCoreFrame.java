package org.lambdacore.gui;

import java.io.PrintWriter;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import java.awt.BorderLayout;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.awt.Color;
import java.awt.Dimension;

import javax.swing.JButton;
import javax.swing.SwingConstants;
import javax.swing.undo.UndoManager;
import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JPopupMenu;
import javax.swing.JTextField;
import javax.swing.JTextPane;
import javax.swing.KeyStroke;
import javax.swing.BoxLayout;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JCheckBox;
import javax.swing.JCheckBoxMenuItem;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;

import org.lambdacore.core.LambdaTermBuilder;
import org.lambdacore.core.LambdaTermBuilder.Binding;
import org.lamcalcj.ast.Lambda.Identifier;
import org.lamcalcj.ast.Lambda.Term;
import org.lamcalcj.parser.syntax.Parser;
import org.lamcalcj.pretty.PrettyPrint;
import org.lamcalcj.pretty.Symbols;
import org.lamcalcj.reducer.BetaReducer;
import org.lamcalcj.reducer.EtaConverter;
import org.lamcalcj.utils.Utils;

import scala.Tuple2;
import scala.collection.JavaConversions;
import scala.util.Either;
import javax.swing.JMenuBar;
import javax.swing.JMenu;
import javax.swing.JMenuItem;
import javax.swing.JSeparator;

public class JLambdaCoreFrame extends JFrame {
	private static final long serialVersionUID = 1L;

	private LambdaTermBuilder lambdaTermBuilder;
	private UndoManager undoManager;
	private JTextField textFieldBetaReduceMaxStep;
	private JTextField textFieldEtaConversionMaxStep;
	private JCheckBoxMenuItem checkBoxMenuItemOmitRedundantGroup;
	private JCheckBoxMenuItem checkBoxMenuItemUncurryingAbstraction;
	private JCheckBoxMenuItem checkBoxMenuItemChainApplication;
	private JCheckBox checkBoxBetaReduceHeadOnly;
	private JCheckBox checkBoxBetaReduceEvaluationOnly;
	private JCheckBox checkBoxEtaConversionHeadOnly;
	private JCheckBox checkBoxEtaConversionEvaluationOnly;
	private JTextPane textPaneInput;
	private JTextPane textPaneOutput;
	private JCheckBoxMenuItem checkBoxMenuItemApply;
	private JPanel panelFunction;
	private JPanel panelNat;
	private JPanel panelBool;
	private JPanel panelMaybe;
	private JPanel panelList;
	private JPanel panelCombinator;
	private JTextField textFieldNumberLiteral;
	private JTextPane textPaneApplyNumberLiteral;

	private int numSave = 8;
	private String[] saveArray;
	private Map<String, Boolean> applyTermMap = new HashMap<>();

	public JLambdaCoreFrame() {
		lambdaTermBuilder = new LambdaTermBuilder();
		lambdaTermBuilder.registerDefaultTerms();

		lambdaTermBuilder.bindingMap.keySet().forEach(variable -> applyTermMap.put(variable, false));

		undoManager = new UndoManager();

		setTitle("LambdaCore - Lambda Calculus Calculator");
		setBounds(100, 100, 1024, 768);
		setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);

		JMenuBar menuBar = new JMenuBar();
		setJMenuBar(menuBar);

		JMenu menuFile = new JMenu("File");
		menuFile.setMnemonic('f');
		menuBar.add(menuFile);

		JMenuItem menuItemExit = new JMenuItem("Exit");
		menuItemExit.setMnemonic('x');
		menuItemExit.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				JLambdaCoreFrame.this.dispose();
			}
		});
		menuFile.add(menuItemExit);

		JMenu menuEdit = new JMenu("Edit");
		menuEdit.setMnemonic('e');
		menuBar.add(menuEdit);

		JMenuItem menuItemUndo = new JMenuItem("Undo");
		menuItemUndo.setMnemonic('u');
		menuItemUndo.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_Z, InputEvent.CTRL_DOWN_MASK));
		menuItemUndo.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				if (undoManager.canUndo())
					undoManager.undo();
			}
		});
		menuEdit.add(menuItemUndo);

		JMenuItem menuItemRedo = new JMenuItem("Redo");
		menuItemRedo.setMnemonic('r');
		menuItemRedo.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_Y, InputEvent.CTRL_DOWN_MASK));
		menuItemRedo.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				if (undoManager.canRedo())
					undoManager.redo();
			}
		});
		menuEdit.add(menuItemRedo);

		menuEdit.add(new JSeparator());

		JMenuItem menuItemLambda = new JMenuItem("Lambda");
		menuItemLambda.setMnemonic('l');
		menuItemLambda.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_L, InputEvent.CTRL_DOWN_MASK));
		menuItemLambda.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				textPaneInput.replaceSelection("λ");
			}
		});
		menuEdit.add(menuItemLambda);

		JMenu menuSource = new JMenu("Source");
		menuSource.setMnemonic('s');
		menuBar.add(menuSource);

		JMenu menuExport = new JMenu("Export");
		menuExport.setMnemonic('o');
		menuSource.add(menuExport);

		JMenuItem menuItemJava = new JMenuItem("Java");
		menuExport.add(menuItemJava);
		menuItemJava.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				try {
					Either<String, Tuple2<scala.collection.immutable.Map<String, Identifier>, Term>> parserResult = Parser
						.parse(new StringReader(applyDependencies(textPaneInput.getText())), Parser.parse$default$2(),
							Parser.parse$default$3());
					if (parserResult.isLeft()) {
						JOptionPane.showMessageDialog(JLambdaCoreFrame.this,
							"Parser Error: " + parserResult.left().get());
						return;
					}
					Term term = parserResult.right().get()._2;
					textPaneOutput.setText("interface L extends Function<L, L> {}\n\n" + PrettyPrint.printLambda(term,
						new Symbols("", "", "", "", "(L) ", "", " -> ", "", "", "", "(", ")", ").apply("), false, false,
						true, PrettyPrint.printLambda$default$6()));
				} catch (Throwable ex) {
					JOptionPane.showMessageDialog(JLambdaCoreFrame.this, "Internal Error: " + ex.toString());
					StringWriter stringWriter = new StringWriter();
					try (PrintWriter printWriter = new PrintWriter(stringWriter)) {
						ex.printStackTrace(printWriter);
					}
					textPaneOutput.setText(stringWriter.toString());
					return;
				}
			}
		});
		menuItemJava.setMnemonic('j');

		JMenuItem menuItemScala = new JMenuItem("Scala");
		menuExport.add(menuItemScala);
		menuItemScala.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				try {
					Either<String, Tuple2<scala.collection.immutable.Map<String, Identifier>, Term>> parserResult = Parser
						.parse(new StringReader(applyDependencies(textPaneInput.getText())), Parser.parse$default$2(),
							Parser.parse$default$3());
					if (parserResult.isLeft()) {
						JOptionPane.showMessageDialog(JLambdaCoreFrame.this,
							"Parser Error: " + parserResult.left().get());
						return;
					}
					Term term = parserResult.right().get()._2;
					textPaneOutput.setText("trait L extends Function[L, L]\n\n" + PrettyPrint.printLambda(term,
						new Symbols("", "", "", "", "", "", " => ", "(", ": L)", "", "(", ")", ")("), false, false,
						true, PrettyPrint.printLambda$default$6()));
				} catch (Throwable ex) {
					JOptionPane.showMessageDialog(JLambdaCoreFrame.this, "Internal Error: " + ex.toString());
					StringWriter stringWriter = new StringWriter();
					try (PrintWriter printWriter = new PrintWriter(stringWriter)) {
						ex.printStackTrace(printWriter);
					}
					textPaneOutput.setText(stringWriter.toString());
					return;
				}
			}
		});
		menuItemScala.setMnemonic('s');

		JMenuItem menuItemClojure = new JMenuItem("Clojure");
		menuExport.add(menuItemClojure);
		menuItemClojure.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				try {
					Either<String, Tuple2<scala.collection.immutable.Map<String, Identifier>, Term>> parserResult = Parser
						.parse(new StringReader(applyDependencies(textPaneInput.getText())), Parser.parse$default$2(),
							Parser.parse$default$3());
					if (parserResult.isLeft()) {
						JOptionPane.showMessageDialog(JLambdaCoreFrame.this,
							"Parser Error: " + parserResult.left().get());
						return;
					}
					Term term = parserResult.right().get()._2;
					textPaneOutput.setText(PrettyPrint.printLambda(term,
						new Symbols("", "", "", "", "(fn ", ")", " ", "[", "]", "", "(", ")", " "), false, false, true,
						PrettyPrint.printLambda$default$6()));
				} catch (Throwable ex) {
					JOptionPane.showMessageDialog(JLambdaCoreFrame.this, "Internal Error: " + ex.toString());
					StringWriter stringWriter = new StringWriter();
					try (PrintWriter printWriter = new PrintWriter(stringWriter)) {
						ex.printStackTrace(printWriter);
					}
					textPaneOutput.setText(stringWriter.toString());
					return;
				}
			}
		});
		menuItemClojure.setMnemonic('c');

		JMenuItem menuItemJavaScript = new JMenuItem("JavaScript");
		menuExport.add(menuItemJavaScript);
		menuItemJavaScript.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				try {
					Either<String, Tuple2<scala.collection.immutable.Map<String, Identifier>, Term>> parserResult = Parser
						.parse(new StringReader(applyDependencies(textPaneInput.getText())), Parser.parse$default$2(),
							Parser.parse$default$3());
					if (parserResult.isLeft()) {
						JOptionPane.showMessageDialog(JLambdaCoreFrame.this,
							"Parser Error: " + parserResult.left().get());
						return;
					}
					Term term = parserResult.right().get()._2;
					textPaneOutput.setText(PrettyPrint.printLambda(term,
						new Symbols("", "", "", "", "", "", " => ", "", "", "", "(", ")", ")("), false, false, true,
						PrettyPrint.printLambda$default$6()));
				} catch (Throwable ex) {
					JOptionPane.showMessageDialog(JLambdaCoreFrame.this, "Internal Error: " + ex.toString());
					StringWriter stringWriter = new StringWriter();
					try (PrintWriter printWriter = new PrintWriter(stringWriter)) {
						ex.printStackTrace(printWriter);
					}
					textPaneOutput.setText(stringWriter.toString());
					return;
				}
			}
		});
		menuItemJavaScript.setMnemonic('a');

		JMenuItem menuItemHaskell = new JMenuItem("Haskell");
		menuExport.add(menuItemHaskell);
		menuItemHaskell.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				try {
					Either<String, Tuple2<scala.collection.immutable.Map<String, Identifier>, Term>> parserResult = Parser
						.parse(new StringReader(applyDependencies(textPaneInput.getText())), Parser.parse$default$2(),
							Parser.parse$default$3());
					if (parserResult.isLeft()) {
						JOptionPane.showMessageDialog(JLambdaCoreFrame.this,
							"Parser Error: " + parserResult.left().get());
						return;
					}
					Term term = parserResult.right().get()._2;
					textPaneOutput.setText(PrettyPrint.printLambda(term,
						new Symbols("(", ")", "", "", "\\", "", "", "", " -> ", " ", "", "", " "), true, true, true,
						PrettyPrint.printLambda$default$6()));
				} catch (Throwable ex) {
					JOptionPane.showMessageDialog(JLambdaCoreFrame.this, "Internal Error: " + ex.toString());
					StringWriter stringWriter = new StringWriter();
					try (PrintWriter printWriter = new PrintWriter(stringWriter)) {
						ex.printStackTrace(printWriter);
					}
					textPaneOutput.setText(stringWriter.toString());
					return;
				}
			}
		});
		menuItemHaskell.setMnemonic('h');

		JMenu menuRun = new JMenu("Run");
		menuRun.setMnemonic('r');
		menuBar.add(menuRun);

		JMenu menuPrettyPrint = new JMenu("PrettyPrint");
		menuPrettyPrint.setMnemonic('p');
		menuRun.add(menuPrettyPrint);

		checkBoxMenuItemOmitRedundantGroup = new JCheckBoxMenuItem("OmitRedundantGroup");
		checkBoxMenuItemOmitRedundantGroup.setMnemonic('o');
		checkBoxMenuItemOmitRedundantGroup.setSelected(true);
		menuPrettyPrint.add(checkBoxMenuItemOmitRedundantGroup);

		checkBoxMenuItemUncurryingAbstraction = new JCheckBoxMenuItem("UncurryingAbstraction");
		checkBoxMenuItemUncurryingAbstraction.setMnemonic('u');
		checkBoxMenuItemUncurryingAbstraction.setSelected(true);
		menuPrettyPrint.add(checkBoxMenuItemUncurryingAbstraction);

		checkBoxMenuItemChainApplication = new JCheckBoxMenuItem("ChainApplication");
		checkBoxMenuItemChainApplication.setMnemonic('c');
		checkBoxMenuItemChainApplication.setSelected(true);
		menuPrettyPrint.add(checkBoxMenuItemChainApplication);

		JMenu menuDependencies = new JMenu("Dependencies");
		menuDependencies.setMnemonic('d');
		menuRun.add(menuDependencies);

		checkBoxMenuItemApply = new JCheckBoxMenuItem("Apply");
		checkBoxMenuItemApply.setMnemonic('a');
		checkBoxMenuItemApply.setSelected(true);
		checkBoxMenuItemApply.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				buildCombinatorPanel();
			}
		});
		menuDependencies.add(checkBoxMenuItemApply);

		JMenuItem menuItemSolve = new JMenuItem("Solve");
		menuItemSolve.setMnemonic('s');
		menuItemSolve.setAccelerator(
			KeyStroke.getKeyStroke(KeyEvent.VK_S, InputEvent.CTRL_DOWN_MASK | InputEvent.SHIFT_DOWN_MASK));
		menuItemSolve.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				try {
					Either<String, Tuple2<scala.collection.immutable.Map<String, Identifier>, Term>> parserResult = Parser
						.parse(new StringReader(applyDependencies(textPaneInput.getText())), Parser.parse$default$2(),
							Parser.parse$default$3());
					if (parserResult.isLeft()) {
						JOptionPane.showMessageDialog(JLambdaCoreFrame.this,
							"Parser Error: " + parserResult.left().get());
						return;
					}
					Term term = parserResult.right().get()._2;
					Set<String> freeVariables = JavaConversions
						.setAsJavaSet(Utils.freeVariables(term, Utils.freeVariables$default$2())).stream()
						.map(Identifier::name).collect(Collectors.toSet());
					Set<String> numberLiteralDependencies = new HashSet<>();
					Set<String> satisfiedDependencies = new HashSet<>();
					Set<String> unsatisfiedDependencies = new HashSet<>();
					freeVariables.forEach(freeVariable -> (lambdaTermBuilder.parseNatLiteral(freeVariable).isPresent()
						? numberLiteralDependencies
						: applyTermMap.containsKey(freeVariable) ? satisfiedDependencies : unsatisfiedDependencies)
							.add(freeVariable));
					int optionSelected = JOptionPane.showConfirmDialog(JLambdaCoreFrame.this,
						"Number literal: " + numberLiteralDependencies + "\n" + "Satisfied: " + satisfiedDependencies
							+ "\n" + "Unsatisfied: " + unsatisfiedDependencies + "\n" + "Apply available dependencies?",
						"Solved new dependencies", JOptionPane.OK_CANCEL_OPTION);
					if (optionSelected == JOptionPane.OK_OPTION) {
						String applyNumberLiteral = numberLiteralDependencies.stream().reduce("",
							(s, lit) -> s + lit + ";");
						if (!textPaneApplyNumberLiteral.getText().isEmpty()
							&& !textPaneApplyNumberLiteral.getText().endsWith(";"))
							applyNumberLiteral = ";" + applyNumberLiteral;
						textPaneApplyNumberLiteral.setText(textPaneApplyNumberLiteral.getText() + applyNumberLiteral);
						satisfiedDependencies.forEach(dependency -> applyTermMap.put(dependency, true));
					}
					buildCombinatorPanel();
				} catch (Throwable ex) {
					JOptionPane.showMessageDialog(JLambdaCoreFrame.this, "Internal Error: " + ex.toString());
					StringWriter stringWriter = new StringWriter();
					try (PrintWriter printWriter = new PrintWriter(stringWriter)) {
						ex.printStackTrace(printWriter);
					}
					textPaneOutput.setText(stringWriter.toString());
					return;
				}
			}
		});
		menuDependencies.add(menuItemSolve);

		JMenuItem menuItemClear = new JMenuItem("Clear");
		menuItemClear.setMnemonic('c');
		menuItemClear.setAccelerator(
			KeyStroke.getKeyStroke(KeyEvent.VK_C, InputEvent.CTRL_DOWN_MASK | InputEvent.SHIFT_DOWN_MASK));
		menuItemClear.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				textPaneApplyNumberLiteral.setText("");
				lambdaTermBuilder.bindingMap.keySet().forEach(variable -> applyTermMap.put(variable, false));
				buildCombinatorPanel();
			}
		});
		menuDependencies.add(menuItemClear);

		JMenu menuHelp = new JMenu("Help");
		menuHelp.setMnemonic('h');
		menuBar.add(menuHelp);

		JMenuItem menuItemAbout = new JMenuItem("About");
		menuItemAbout.setMnemonic('a');
		menuItemAbout.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				JOptionPane.showMessageDialog(JLambdaCoreFrame.this,
					"LambdaCore - Lambda Calculus Calculator\n\nAuthor: Yu Xuanchi (yuxuanchiadm@126.com)");
			}
		});
		menuHelp.add(menuItemAbout);

		panelCombinator = new JPanel();
		getContentPane().add(panelCombinator, BorderLayout.NORTH);
		panelCombinator.setLayout(new BoxLayout(panelCombinator, BoxLayout.Y_AXIS));

		panelFunction = new JPanel();
		panelFunction.setBackground(Color.GREEN);
		FlowLayout fl_panelFunction = (FlowLayout) panelFunction.getLayout();
		fl_panelFunction.setAlignment(FlowLayout.LEFT);
		panelCombinator.add(panelFunction);

		panelNat = new JPanel();
		FlowLayout fl_panelNat = (FlowLayout) panelNat.getLayout();
		fl_panelNat.setAlignment(FlowLayout.LEFT);
		panelNat.setBackground(Color.CYAN);
		panelCombinator.add(panelNat);

		panelBool = new JPanel();
		FlowLayout fl_panelBool = (FlowLayout) panelBool.getLayout();
		fl_panelBool.setAlignment(FlowLayout.LEFT);
		panelBool.setBackground(Color.ORANGE);
		panelCombinator.add(panelBool);

		panelMaybe = new JPanel();
		FlowLayout fl_panelMaybe = (FlowLayout) panelMaybe.getLayout();
		fl_panelMaybe.setAlignment(FlowLayout.LEFT);
		panelMaybe.setBackground(Color.LIGHT_GRAY);
		panelCombinator.add(panelMaybe);

		panelList = new JPanel();
		FlowLayout fl_panelList = (FlowLayout) panelList.getLayout();
		fl_panelList.setAlignment(FlowLayout.LEFT);
		panelList.setBackground(Color.PINK);
		panelCombinator.add(panelList);

		JPanel panelControl = new JPanel();
		getContentPane().add(panelControl, BorderLayout.SOUTH);
		panelControl.setLayout(new BoxLayout(panelControl, BoxLayout.Y_AXIS));

		JPanel panelReduction = new JPanel();
		panelControl.add(panelReduction);

		JPanel panelBetaReduce = new JPanel();
		panelBetaReduce.setBackground(Color.ORANGE);
		panelReduction.add(panelBetaReduce);

		JLabel lblBetaReduceMaxStep = new JLabel("MaxStep:");
		panelBetaReduce.add(lblBetaReduceMaxStep);

		textFieldBetaReduceMaxStep = new JTextField();
		textFieldBetaReduceMaxStep.setText("255");
		panelBetaReduce.add(textFieldBetaReduceMaxStep);
		textFieldBetaReduceMaxStep.setColumns(10);

		checkBoxBetaReduceHeadOnly = new JCheckBox("HeadOnly");
		panelBetaReduce.add(checkBoxBetaReduceHeadOnly);

		checkBoxBetaReduceEvaluationOnly = new JCheckBox("EvaluationOnly");
		panelBetaReduce.add(checkBoxBetaReduceEvaluationOnly);

		JButton buttonBetaReduce = new JButton("Beta Reduce");
		buttonBetaReduce.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				try {
					int maxStep;
					try {
						maxStep = Integer.parseInt(textFieldBetaReduceMaxStep.getText());
					} catch (NumberFormatException ex) {
						JOptionPane.showMessageDialog(JLambdaCoreFrame.this, "Can not parse max step");
						return;
					}
					boolean headOnly = checkBoxBetaReduceHeadOnly.isSelected();
					boolean evaluationOnly = checkBoxBetaReduceEvaluationOnly.isSelected();
					boolean omitRedundantGroup = checkBoxMenuItemOmitRedundantGroup.isSelected();
					boolean uncurryingAbstraction = checkBoxMenuItemUncurryingAbstraction.isSelected();
					boolean chainApplication = checkBoxMenuItemChainApplication.isSelected();
					Either<String, Tuple2<scala.collection.immutable.Map<String, Identifier>, Term>> parserResult = Parser
						.parse(new StringReader(applyDependencies(textPaneInput.getText())), Parser.parse$default$2(),
							Parser.parse$default$3());
					if (parserResult.isLeft()) {
						JOptionPane.showMessageDialog(JLambdaCoreFrame.this,
							"Parser Error: " + parserResult.left().get());
						return;
					}
					Term term = parserResult.right().get()._2;
					Tuple2<Object, Term> betaReducerResult = BetaReducer.betaReduction(term, maxStep, headOnly,
						evaluationOnly);
					if (!betaReducerResult._1.equals(Boolean.TRUE))
						JOptionPane.showMessageDialog(JLambdaCoreFrame.this,
							"Beta reducer not halt in " + maxStep + " step");
					Term resultTerm = betaReducerResult._2;
					textPaneOutput.setText(
						PrettyPrint.printLambda(resultTerm, PrettyPrint.printLambda$default$2(), omitRedundantGroup,
							uncurryingAbstraction, chainApplication, PrettyPrint.printLambda$default$6()));
				} catch (Throwable ex) {
					JOptionPane.showMessageDialog(JLambdaCoreFrame.this, "Internal Error: " + ex.toString());
					StringWriter stringWriter = new StringWriter();
					try (PrintWriter printWriter = new PrintWriter(stringWriter)) {
						ex.printStackTrace(printWriter);
					}
					textPaneOutput.setText(stringWriter.toString());
					return;
				}
			}
		});
		panelBetaReduce.add(buttonBetaReduce);

		JPanel panelEtaConversion = new JPanel();
		panelEtaConversion.setBackground(Color.GREEN);
		panelReduction.add(panelEtaConversion);

		JLabel lblEtaConversionMaxStep = new JLabel("MaxStep:");
		panelEtaConversion.add(lblEtaConversionMaxStep);

		textFieldEtaConversionMaxStep = new JTextField();
		textFieldEtaConversionMaxStep.setText("2147483647");
		textFieldEtaConversionMaxStep.setColumns(10);
		panelEtaConversion.add(textFieldEtaConversionMaxStep);

		checkBoxEtaConversionHeadOnly = new JCheckBox("HeadOnly");
		panelEtaConversion.add(checkBoxEtaConversionHeadOnly);

		checkBoxEtaConversionEvaluationOnly = new JCheckBox("EvaluationOnly");
		panelEtaConversion.add(checkBoxEtaConversionEvaluationOnly);

		JButton buttonEtaConversion = new JButton("Eta Conversion");
		buttonEtaConversion.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				try {
					int maxStep;
					try {
						maxStep = Integer.parseInt(textFieldEtaConversionMaxStep.getText());
					} catch (NumberFormatException ex) {
						JOptionPane.showMessageDialog(JLambdaCoreFrame.this, "Can not parse max step");
						return;
					}
					boolean headOnly = checkBoxEtaConversionHeadOnly.isSelected();
					boolean evaluationOnly = checkBoxEtaConversionEvaluationOnly.isSelected();
					boolean omitRedundantGroup = checkBoxMenuItemOmitRedundantGroup.isSelected();
					boolean uncurryingAbstraction = checkBoxMenuItemUncurryingAbstraction.isSelected();
					boolean chainApplication = checkBoxMenuItemChainApplication.isSelected();
					Either<String, Tuple2<scala.collection.immutable.Map<String, Identifier>, Term>> parserResult = Parser
						.parse(new StringReader(applyDependencies(textPaneInput.getText())), Parser.parse$default$2(),
							Parser.parse$default$3());
					if (parserResult.isLeft()) {
						JOptionPane.showMessageDialog(JLambdaCoreFrame.this,
							"Parser Error: " + parserResult.left().get());
						return;
					}
					Term term = parserResult.right().get()._2;
					Tuple2<Object, Term> etaConverterResult = EtaConverter.etaConversion(term, maxStep, headOnly,
						evaluationOnly);
					if (!etaConverterResult._1.equals(Boolean.TRUE))
						JOptionPane.showMessageDialog(JLambdaCoreFrame.this,
							"Eta converter not halt in " + maxStep + " step");
					Term resultTerm = etaConverterResult._2;
					textPaneOutput.setText(
						PrettyPrint.printLambda(resultTerm, PrettyPrint.printLambda$default$2(), omitRedundantGroup,
							uncurryingAbstraction, chainApplication, PrettyPrint.printLambda$default$6()));
				} catch (Throwable ex) {
					JOptionPane.showMessageDialog(JLambdaCoreFrame.this, "Internal Error: " + ex.toString());
					StringWriter stringWriter = new StringWriter();
					try (PrintWriter printWriter = new PrintWriter(stringWriter)) {
						ex.printStackTrace(printWriter);
					}
					textPaneOutput.setText(stringWriter.toString());
					return;
				}
			}
		});
		panelEtaConversion.add(buttonEtaConversion);

		JSplitPane splitPaneLambdaTerm = new JSplitPane();
		splitPaneLambdaTerm.setResizeWeight(0.5);
		getContentPane().add(splitPaneLambdaTerm, BorderLayout.CENTER);

		JPanel panelInput = new JPanel();
		splitPaneLambdaTerm.setLeftComponent(panelInput);
		panelInput.setLayout(new BorderLayout(0, 0));

		JLabel lblInput = new JLabel("Input");
		lblInput.setHorizontalAlignment(SwingConstants.CENTER);
		panelInput.add(lblInput, BorderLayout.NORTH);

		JScrollPane scrollPaneInput = new JScrollPane();
		panelInput.add(scrollPaneInput, BorderLayout.CENTER);

		textPaneInput = new JTextPane();
		textPaneInput.getDocument().addUndoableEditListener(undoManager);
		scrollPaneInput.setViewportView(textPaneInput);

		JPanel panelOutput = new JPanel();
		splitPaneLambdaTerm.setRightComponent(panelOutput);
		panelOutput.setLayout(new BorderLayout(0, 0));

		JLabel lblOutput = new JLabel("Output");
		lblOutput.setHorizontalAlignment(SwingConstants.CENTER);
		panelOutput.add(lblOutput, BorderLayout.NORTH);

		JScrollPane scrollPaneOutput = new JScrollPane();
		panelOutput.add(scrollPaneOutput, BorderLayout.CENTER);

		textPaneOutput = new JTextPane();
		textPaneOutput.setEditable(false);
		scrollPaneOutput.setViewportView(textPaneOutput);

		JPanel panelSave = new JPanel();
		getContentPane().add(panelSave, BorderLayout.WEST);
		panelSave.setLayout(new BoxLayout(panelSave, BoxLayout.Y_AXIS));

		saveArray = new String[numSave];

		for (int i = 0; i < numSave; i++) {
			final int currentSaveSlot = i;
			JButton buttonSave = new JButton("Save" + currentSaveSlot);
			buttonSave.addActionListener(new ActionListener() {
				@Override
				public void actionPerformed(ActionEvent e) {
					saveArray[currentSaveSlot] = textPaneInput.getText();
				}
			});
			panelSave.add(buttonSave);
		}

		JPanel panelLoad = new JPanel();
		getContentPane().add(panelLoad, BorderLayout.EAST);
		panelLoad.setLayout(new BoxLayout(panelLoad, BoxLayout.Y_AXIS));

		for (int i = 0; i < numSave; i++) {
			final int currentSaveSlot = i;
			JButton buttonLoad = new JButton("Load" + currentSaveSlot);
			buttonLoad.addActionListener(new ActionListener() {
				@Override
				public void actionPerformed(ActionEvent e) {
					if (saveArray[currentSaveSlot] != null)
						textPaneInput.setText(saveArray[currentSaveSlot]);
				}
			});
			panelLoad.add(buttonLoad);
		}

		textFieldNumberLiteral = new JTextField("0");
		textPaneApplyNumberLiteral = new JTextPane();
		textPaneApplyNumberLiteral.setText("#0; #1;\n#2 - 3");

		buildCombinatorPanel();
	}

	public void buildCombinatorPanel() {
		boolean isApplyDependencies = checkBoxMenuItemApply.isSelected();

		Set<String> functionCombinatorSet = lambdaTermBuilder.categoryMap.get("function");
		Set<String> natCombinatorSet = lambdaTermBuilder.categoryMap.get("nat");
		Set<String> boolCombinatorSet = lambdaTermBuilder.categoryMap.get("bool");
		Set<String> maybeCombinatorSet = lambdaTermBuilder.categoryMap.get("maybe");
		Set<String> listCombinatorSet = lambdaTermBuilder.categoryMap.get("list");

		panelFunction.removeAll();
		panelFunction.add(new JLabel("Function:"));
		addCombinator(isApplyDependencies, panelFunction, functionCombinatorSet);

		panelNat.removeAll();
		panelNat.add(new JLabel("Nat:"));
		addNumberLiteral(isApplyDependencies, panelNat);
		addCombinator(isApplyDependencies, panelNat, natCombinatorSet);

		panelBool.removeAll();
		panelBool.add(new JLabel("Bool:"));
		addCombinator(isApplyDependencies, panelBool, boolCombinatorSet);

		panelMaybe.removeAll();
		panelMaybe.add(new JLabel("Maybe:"));
		addCombinator(isApplyDependencies, panelMaybe, maybeCombinatorSet);

		panelList.removeAll();
		panelList.add(new JLabel("List:"));
		addCombinator(isApplyDependencies, panelList, listCombinatorSet);

		panelCombinator.revalidate();
	}

	public void addCombinator(boolean isApplyDependencies, JPanel panel, Set<String> combinatorSet) {
		for (String combinator : combinatorSet) {
			if (isApplyDependencies) {
				Binding binding = lambdaTermBuilder.bindingMap.get(combinator);
				JCheckBox checkBox = new JCheckBox(combinator, applyTermMap.get(combinator));
				checkBox.setToolTipText(binding.getVariable()
					+ Optional.ofNullable(binding.getType()).map(type -> " : " + type).orElse(""));
				checkBox.addActionListener(new ActionListener() {
					@Override
					public void actionPerformed(ActionEvent e) {
						applyTermMap.put(combinator, checkBox.isSelected());
					}
				});
				panel.add(checkBox);
			} else {
				Binding binding = lambdaTermBuilder.bindingMap.get(combinator);
				JButton button = new JButton(combinator);
				button.setToolTipText(binding.getVariable()
					+ Optional.ofNullable(binding.getType()).map(type -> " : " + type).orElse(""));
				button.addActionListener(new ActionListener() {

					@Override
					public void actionPerformed(ActionEvent e) {
						textPaneInput.setText(lambdaTermBuilder.bindingMap.get(combinator).getTerm());
					}
				});
				panel.add(button);
			}
		}
	}

	public void addNumberLiteral(boolean isApplyDependencies, JPanel panel) {
		if (isApplyDependencies) {
			JButton button = new JButton("literal");
			panel.add(button);

			JPopupMenu popupMenu = new JPopupMenu();
			button.addActionListener(new ActionListener() {
				@Override
				public void actionPerformed(ActionEvent e) {
					popupMenu.show(button, button.getX(), button.getY());
				}
			});

			JScrollPane scrollPane = new JScrollPane();
			popupMenu.add(scrollPane);

			textPaneApplyNumberLiteral.setPreferredSize(new Dimension(400, 200));
			scrollPane.setViewportView(textPaneApplyNumberLiteral);
		} else {
			textFieldNumberLiteral.setColumns(10);
			panel.add(textFieldNumberLiteral);

			JButton button = new JButton("encodeLiteral");
			button.addActionListener(new ActionListener() {
				public void actionPerformed(ActionEvent e) {
					int lit;
					try {
						lit = Integer.parseInt(textFieldNumberLiteral.getText());
					} catch (NumberFormatException ex) {
						JOptionPane.showMessageDialog(JLambdaCoreFrame.this, "Can not parse number literal");
						return;
					}
					String result = lambdaTermBuilder.buildNatLiteral(lit);
					textPaneInput.setText(result);
				}
			});
			panel.add(button);
		}
	}

	public Set<String> getApplyNumberLiteral() {
		Set<String> applyNumberLiteral = new HashSet<>();
		for (String pat : textPaneApplyNumberLiteral.getText().split(";")) {
			pat = pat.trim();
			if (pat.isEmpty() || (pat.startsWith("#")))
				continue;
			int rangeSplitterIndex = pat.indexOf('-');
			if (rangeSplitterIndex == -1) {
				int lit;
				try {
					lit = Integer.parseUnsignedInt(pat.trim());
				} catch (NumberFormatException ex) {
					JOptionPane.showMessageDialog(this, "Illegal apply number literal syntax");
					return new HashSet<>();
				}
				applyNumberLiteral.add(Integer.toString(lit));
			} else if (pat.indexOf('-', rangeSplitterIndex + 1) == -1) {
				int start;
				int end;
				try {
					start = Integer.parseUnsignedInt(pat.substring(0, rangeSplitterIndex).trim());
					end = Integer.parseUnsignedInt(pat.substring(rangeSplitterIndex + 1, pat.length()).trim());
				} catch (NumberFormatException ex) {
					JOptionPane.showMessageDialog(this, "Illegal apply number literal syntax");
					return new HashSet<>();
				}
				for (int i = start; i <= end; i++)
					applyNumberLiteral.add(Integer.toString(i));
			} else {
				JOptionPane.showMessageDialog(this, "Illegal apply number literal syntax");
				return new HashSet<>();
			}
		}
		return applyNumberLiteral;
	}

	public String applyDependencies(String term) {
		if (!checkBoxMenuItemApply.isSelected())
			return term;
		Set<String> dependencies = applyTermMap.entrySet().stream().filter(Entry::getValue).map(Entry::getKey)
			.collect(Collectors.toCollection(HashSet::new));
		dependencies.addAll(getApplyNumberLiteral());
		return lambdaTermBuilder.buildTerm(term, dependencies);
	}
}
