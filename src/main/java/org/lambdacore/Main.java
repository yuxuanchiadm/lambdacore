package org.lambdacore;

import javax.swing.SwingUtilities;

import org.lambdacore.gui.JLambdaCoreFrame;

public class Main {
	public static void main(String[] args) {
		SwingUtilities.invokeLater(new Runnable() {
			@Override
			public void run() {
				JLambdaCoreFrame lambdaCoreFrame = new JLambdaCoreFrame();
				lambdaCoreFrame.setVisible(true);
			}
		});
	}
}
