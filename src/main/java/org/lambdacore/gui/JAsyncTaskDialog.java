package org.lambdacore.gui;

import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JPanel;
import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.lang.reflect.InvocationTargetException;
import java.util.concurrent.ExecutionException;
import java.util.function.Function;

import javax.swing.JLabel;
import javax.swing.JProgressBar;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.SwingUtilities;
import javax.swing.SwingWorker;

public class JAsyncTaskDialog<T> extends JDialog {
	private static final long serialVersionUID = 1L;

	private final Function<ProgressRepoter, T> task;

	private JTextArea textAreaMessage;
	private JButton buttonClose;
	private JLabel labelMessage;
	private JProgressBar progressBar;

	public JAsyncTaskDialog(JFrame parentFrame, String title, Function<ProgressRepoter, T> task) {
		super(parentFrame);
		setDefaultCloseOperation(JDialog.DO_NOTHING_ON_CLOSE);

		this.task = task;

		setTitle(title);
		setModal(true);
		setType(Type.POPUP);
		setMinimumSize(new Dimension(400, 250));
		setPreferredSize(new Dimension(400, 250));
		setLocation(parentFrame.getX() + parentFrame.getWidth() / 2 - 400 / 2,
			parentFrame.getY() + parentFrame.getHeight() / 2 - 250 / 2);

		getContentPane().setLayout(new BoxLayout(getContentPane(), BoxLayout.X_AXIS));

		JPanel panelMain = new JPanel();
		getContentPane().add(panelMain);
		panelMain.setLayout(new BorderLayout(0, 0));

		JPanel panelProgress = new JPanel();
		panelMain.add(panelProgress, BorderLayout.NORTH);

		JLabel labelProgress = new JLabel("Progress:");
		panelProgress.add(labelProgress);

		progressBar = new JProgressBar(0, 0);
		panelProgress.add(progressBar);

		labelMessage = new JLabel("(" + progressBar.getValue() + "/" + progressBar.getMaximum() + ")");
		panelProgress.add(labelMessage);

		JScrollPane scrollPaneMessage = new JScrollPane();
		panelMain.add(scrollPaneMessage, BorderLayout.CENTER);

		textAreaMessage = new JTextArea();
		textAreaMessage.setEditable(false);
		scrollPaneMessage.setViewportView(textAreaMessage);

		JPanel panelButton = new JPanel();
		panelMain.add(panelButton, BorderLayout.SOUTH);

		buttonClose = new JButton("Close");
		buttonClose.setEnabled(false);
		buttonClose.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				dispose();
			}
		});
		panelButton.add(buttonClose);

		addWindowListener(new WindowAdapter() {
			@Override
			public void windowClosing(WindowEvent e) {
				if (buttonClose.isEnabled())
					dispose();
			}
		});

		pack();
	}

	public T execute() {
		ProgressRepoter repoter = new ProgressRepoter() {
			@Override
			public void setTotolProgress(int progress) {
				try {
					SwingUtilities.invokeAndWait(() -> {
						progressBar.setMaximum(progress);
						labelMessage.setText("(" + progressBar.getValue() + "/" + progressBar.getMaximum() + ")");
					});
				} catch (InvocationTargetException e) {
					e.printStackTrace();
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
			}

			@Override
			public void setCurrentProgress(int progress) {
				try {
					SwingUtilities.invokeAndWait(() -> {
						progressBar.setValue(progress);
						labelMessage.setText("(" + progressBar.getValue() + "/" + progressBar.getMaximum() + ")");
					});
				} catch (InvocationTargetException e) {
					e.printStackTrace();
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
			}

			@Override
			public void setCompleted(boolean completed) {
				try {
					SwingUtilities.invokeAndWait(() -> {
						buttonClose.setEnabled(completed);
					});
				} catch (InvocationTargetException e) {
					e.printStackTrace();
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
			}

			@Override
			public void sendMessage(String msg) {
				try {
					SwingUtilities.invokeAndWait(() -> {
						textAreaMessage.append(msg + "\n");
					});
				} catch (InvocationTargetException e) {
					e.printStackTrace();
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
			}
		};

		SwingWorker<T, Void> worker = new SwingWorker<T, Void>() {
			@Override
			protected T doInBackground() {
				return task.apply(repoter);
			}
		};

		worker.execute();
		setVisible(true);

		try {
			return worker.get();
		} catch (InterruptedException e) {
			throw new RuntimeException(e);
		} catch (ExecutionException e) {
			throw new RuntimeException(e);
		}
	}

	public interface ProgressRepoter {
		void setTotolProgress(int progress);

		void setCurrentProgress(int progress);

		void sendMessage(String msg);

		void setCompleted(boolean completed);
	}
}
