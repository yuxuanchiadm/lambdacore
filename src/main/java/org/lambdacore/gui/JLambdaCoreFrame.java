package org.lambdacore.gui;

import java.io.StringReader;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import java.awt.BorderLayout;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyAdapter;
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
import javax.swing.BoxLayout;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JCheckBox;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;

import org.lambdacore.core.LambdaTermBuilder;

import org.lamcalcj.ast.Lambda.Identifier;
import org.lamcalcj.ast.Lambda.Term;
import org.lamcalcj.parser.syntax.Parser;
import org.lamcalcj.pretty.PrettyPrint;
import org.lamcalcj.reducer.BetaReducer;
import org.lamcalcj.reducer.EtaConverter;

import scala.Tuple2;
import scala.util.Either;

public class JLambdaCoreFrame extends JFrame {
	private static final long serialVersionUID = 1L;

	private LambdaTermBuilder lambdaTermBuilder;
	private UndoManager undoManager;
	private JTextField textFieldBetaReduceMaxStep;
	private JTextField textFieldEtaConversionMaxStep;
	private JCheckBox checkBoxOmitRedundantGroup;
	private JCheckBox checkBoxUncurryingAbstraction;
	private JCheckBox checkBoxChainApplication;
	private JCheckBox checkBoxBetaReduceHeadOnly;
	private JCheckBox checkBoxBetaReduceEvaluationOnly;
	private JCheckBox checkBoxEtaConversionHeadOnly;
	private JCheckBox checkBoxEtaConversionEvaluationOnly;
	private JTextPane textPaneInput;
	private JTextPane textPaneOutput;
	private JCheckBox checkBoxApplyTerm;
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

		JPanel panelPrettyPrint = new JPanel();
		FlowLayout flowLayout_5 = (FlowLayout) panelPrettyPrint.getLayout();
		flowLayout_5.setAlignment(FlowLayout.LEFT);
		panelControl.add(panelPrettyPrint);

		JLabel lblPrettyPrint = new JLabel("PrettyPrint:");
		panelPrettyPrint.add(lblPrettyPrint);

		checkBoxOmitRedundantGroup = new JCheckBox("OmitRedundantGroup");
		checkBoxOmitRedundantGroup.setSelected(true);
		panelPrettyPrint.add(checkBoxOmitRedundantGroup);

		checkBoxUncurryingAbstraction = new JCheckBox("UncurryingAbstraction");
		checkBoxUncurryingAbstraction.setSelected(true);
		panelPrettyPrint.add(checkBoxUncurryingAbstraction);

		checkBoxChainApplication = new JCheckBox("ChainApplication");
		checkBoxChainApplication.setSelected(true);
		panelPrettyPrint.add(checkBoxChainApplication);

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
				int maxStep;
				try {
					maxStep = Integer.parseInt(textFieldBetaReduceMaxStep.getText());
				} catch (NumberFormatException ex) {
					JOptionPane.showMessageDialog(null, "Can not parse max step");
					return;
				}
				boolean headOnly = checkBoxBetaReduceHeadOnly.isSelected();
				boolean evaluationOnly = checkBoxBetaReduceEvaluationOnly.isSelected();
				boolean omitRedundantGroup = checkBoxOmitRedundantGroup.isSelected();
				boolean uncurryingAbstraction = checkBoxUncurryingAbstraction.isSelected();
				boolean chainApplication = checkBoxChainApplication.isSelected();
				Either<String, Tuple2<scala.collection.immutable.Map<String, Identifier>, Term>> result = Parser.parse(
					new StringReader(applyTerm(textPaneInput.getText())), Parser.parse$default$2(),
					Parser.parse$default$3());
				if (result.isLeft()) {
					JOptionPane.showMessageDialog(null, "Parser Error: " + result.left().get());
					return;
				}
				Term term = result.right().get()._2;
				Term resultTerm = BetaReducer.betaReduction(term, maxStep, headOnly, evaluationOnly)._2;
				textPaneOutput.setText(PrettyPrint.printLambda(resultTerm, PrettyPrint.printLambda$default$2(),
					omitRedundantGroup, uncurryingAbstraction, chainApplication, PrettyPrint.printLambda$default$6()));
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
				int maxStep;
				try {
					maxStep = Integer.parseInt(textFieldEtaConversionMaxStep.getText());
				} catch (NumberFormatException ex) {
					JOptionPane.showMessageDialog(null, "Can not parse max step");
					return;
				}
				boolean headOnly = checkBoxEtaConversionHeadOnly.isSelected();
				boolean evaluationOnly = checkBoxEtaConversionEvaluationOnly.isSelected();
				boolean omitRedundantGroup = checkBoxOmitRedundantGroup.isSelected();
				boolean uncurryingAbstraction = checkBoxUncurryingAbstraction.isSelected();
				boolean chainApplication = checkBoxChainApplication.isSelected();
				Either<String, Tuple2<scala.collection.immutable.Map<String, Identifier>, Term>> result = Parser.parse(
					new StringReader(applyTerm(textPaneInput.getText())), Parser.parse$default$2(),
					Parser.parse$default$3());
				if (result.isLeft()) {
					JOptionPane.showMessageDialog(null, "Parser Error: " + result.left().get());
					return;
				}
				Term term = result.right().get()._2;
				Term resultTerm = EtaConverter.etaConversion(term, maxStep, headOnly, evaluationOnly)._2;
				textPaneOutput.setText(PrettyPrint.printLambda(resultTerm, PrettyPrint.printLambda$default$2(),
					omitRedundantGroup, uncurryingAbstraction, chainApplication, PrettyPrint.printLambda$default$6()));
			}
		});
		panelEtaConversion.add(buttonEtaConversion);

		JPanel panelOther = new JPanel();
		FlowLayout fl_panelOther = (FlowLayout) panelOther.getLayout();
		fl_panelOther.setAlignment(FlowLayout.LEFT);
		panelControl.add(panelOther);

		JButton buttonLambda = new JButton("Lambda");
		buttonLambda.setToolTipText("Ctrl+L");
		buttonLambda.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				textPaneInput.replaceSelection("λ");
			}
		});

		checkBoxApplyTerm = new JCheckBox("ApplyTerm");
		checkBoxApplyTerm.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				buildCombinatorPanel();
			}
		});
		panelOther.add(checkBoxApplyTerm);

		JButton buttonUndo = new JButton("Undo");
		buttonUndo.setToolTipText("Ctrl+Z");
		buttonUndo.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				if (undoManager.canUndo())
					undoManager.undo();
			}
		});
		panelOther.add(buttonUndo);

		JButton buttonRedo = new JButton("Redo");
		buttonRedo.setToolTipText("Ctrl+Y");
		buttonRedo.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				if (undoManager.canRedo())
					undoManager.redo();
			}
		});
		panelOther.add(buttonRedo);
		panelOther.add(buttonLambda);

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
		textPaneInput.addKeyListener(new KeyAdapter() {
			@Override
			public void keyPressed(KeyEvent e) {
				if (e.isControlDown())
					if (e.getKeyCode() == KeyEvent.VK_Z && undoManager.canUndo())
						undoManager.undo();
					else if (e.getKeyCode() == KeyEvent.VK_Y && undoManager.canRedo())
						undoManager.redo();
					else if (e.getKeyCode() == KeyEvent.VK_L)
						textPaneInput.replaceSelection("λ");
			}
		});
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

		buildCombinatorPanel();
	}

	public void buildCombinatorPanel() {
		boolean isApplyTerm = checkBoxApplyTerm.isSelected();

		Set<String> functionCombinatorSet = lambdaTermBuilder.categoryMap.get("function");
		Set<String> natCombinatorSet = lambdaTermBuilder.categoryMap.get("nat");
		Set<String> boolCombinatorSet = lambdaTermBuilder.categoryMap.get("bool");
		Set<String> maybeCombinatorSet = lambdaTermBuilder.categoryMap.get("maybe");
		Set<String> listCombinatorSet = lambdaTermBuilder.categoryMap.get("list");

		panelFunction.removeAll();
		panelFunction.add(new JLabel("Function:"));
		addCombinator(isApplyTerm, panelFunction, functionCombinatorSet);

		panelNat.removeAll();
		panelNat.add(new JLabel("Nat:"));
		addNumberLiteral(isApplyTerm, panelNat);
		addCombinator(isApplyTerm, panelNat, natCombinatorSet);

		panelBool.removeAll();
		panelBool.add(new JLabel("Bool:"));
		addCombinator(isApplyTerm, panelBool, boolCombinatorSet);

		panelMaybe.removeAll();
		panelMaybe.add(new JLabel("Maybe:"));
		addCombinator(isApplyTerm, panelMaybe, maybeCombinatorSet);

		panelList.removeAll();
		panelList.add(new JLabel("List:"));
		addCombinator(isApplyTerm, panelList, listCombinatorSet);

		panelCombinator.revalidate();
	}

	public void addCombinator(boolean isApplyTerm, JPanel panel, Set<String> combinatorSet) {
		for (String combinator : combinatorSet) {
			if (isApplyTerm) {
				JCheckBox checkBox = new JCheckBox(combinator, applyTermMap.get(combinator));
				checkBox.addActionListener(new ActionListener() {
					@Override
					public void actionPerformed(ActionEvent e) {
						applyTermMap.put(combinator, checkBox.isSelected());
					}
				});
				panel.add(checkBox);
			} else {
				JButton button = new JButton(combinator);
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

	public void addNumberLiteral(boolean isApplyTerm, JPanel panel) {
		if (isApplyTerm) {
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
						JOptionPane.showMessageDialog(null, "Can not parse number literal");
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
		for (String pat : textPaneApplyNumberLiteral.getText().replaceAll("\\s", "").split(";")) {
			if (pat.isEmpty())
				continue;
			int rangeSplitterIndex = pat.indexOf('-');
			if (rangeSplitterIndex == -1) {
				int lit;
				try {
					lit = Integer.parseInt(pat);
				} catch (NumberFormatException ex) {
					JOptionPane.showMessageDialog(null, "Illegal apply number literal syntax");
					return new HashSet<>();
				}
				applyNumberLiteral.add(Integer.toString(lit));
			} else if (pat.indexOf('-', rangeSplitterIndex + 1) == -1) {
				int start;
				int end;
				try {
					start = Integer.parseInt(pat.substring(0, rangeSplitterIndex));
					end = Integer.parseInt(pat.substring(rangeSplitterIndex + 1, pat.length()));
				} catch (NumberFormatException ex) {
					JOptionPane.showMessageDialog(null, "Illegal apply number literal syntax");
					return new HashSet<>();
				}
				for (int i = start; i <= end; i++)
					applyNumberLiteral.add(Integer.toString(i));
			} else {
				JOptionPane.showMessageDialog(null, "Illegal apply number literal syntax");
				return new HashSet<>();
			}
		} ;
		return applyNumberLiteral;
	}

	public String applyTerm(String term) {
		if (!checkBoxApplyTerm.isSelected())
			return term;
		Set<String> dependencies = applyTermMap.entrySet().stream().filter(Entry::getValue).map(Entry::getKey)
			.collect(Collectors.toCollection(HashSet::new));
		dependencies.addAll(getApplyNumberLiteral());
		return lambdaTermBuilder.buildTerm(term, dependencies);
	}
}
