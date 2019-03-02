package org.lambdacore.utils;

import java.util.concurrent.TimeUnit;

public final class Timer {
	private final long startTime;
	private long lastTime;
	private StringBuilder message;

	public Timer() {
		startTime = System.nanoTime();
		lastTime = startTime;
		message = new StringBuilder();
	}

	public void next(String taskName) {
		long currentTime = System.nanoTime();
		long elapsedTime = currentTime - lastTime;
		lastTime = currentTime;
		message.append(taskName);
		message.append(": ");
		message.append(TimeUnit.NANOSECONDS.toMillis(elapsedTime));
		message.append(" ms");
		message.append('\n');
	}

	public String toMessage() {
		long elapsedTime = lastTime - startTime;
		message.append("Total: ");
		message.append(TimeUnit.NANOSECONDS.toMillis(elapsedTime));
		message.append(" ms");
		return message.toString();
	}
}
