import matplotlib.pyplot as plt
from matplotlib.widgets import Button
from matplotlib import animation
from matplotlib.animation import FFMpegWriter, PillowWriter
import os

from matplotlib.animation import FFMpegWriter
print(FFMpegWriter)



EXPORT_DIR = "exported_data"
os.makedirs(EXPORT_DIR, exist_ok=True)

# Parameters
bar_width = 0.8
colors = {1: 'red', 0: 'green'}

# Global state
cycles = []
discovered = []
states = []
n = 2

fig, ax = plt.subplots()
plt.subplots_adjust(bottom=0.25)

current_index = [0]
auto_play = [False]

def prepare_states(max_n):
    global cycles, discovered, states, n
    cycles = []
    discovered = []
    states = []
    n = 2

    while n <= max_n:
        # Rotate all existing cycles
        for i in range(len(cycles)):
            cycles[i] = cycles[i][1:] + [cycles[i][0]]

        # Check elimination
        is_eliminated = any(c[0] == 1 for c in cycles)

        # Add new cycle if not eliminated
        if not is_eliminated:
            new_cycle = [1] + [0] * (n - 1)
            cycles.append(new_cycle.copy())
            discovered.append(n)

        # Save snapshot state
        states.append((n, [c.copy() for c in cycles], discovered.copy()))
        n += 1


def draw_state(index):
    ax.clear()
    n_val, cycles_snapshot, discovered_snapshot = states[index]

    ax.set_ylim(0, max(len(c) for c in cycles_snapshot) + 1)
    ax.set_xlim(-0.5, len(cycles_snapshot) - 0.5)
    ax.set_title(f"Elimination cycles: n = {n_val}")
    ax.set_xlabel("Cycle (number)")
    ax.set_ylabel("Positions")
    ax.set_xticks(range(len(cycles_snapshot)))
    ax.set_xticklabels(discovered_snapshot)

    for i, cycle in enumerate(cycles_snapshot):
        for j, bit in enumerate(cycle):
            ax.bar(i, 1, bottom=j, color=colors[bit], width=bar_width)

    fig.canvas.draw_idle()


def forward(event=None):
    if current_index[0] < len(states) - 1:
        current_index[0] += 1
        draw_state(current_index[0])


def backward(event):
    if current_index[0] > 0:
        current_index[0] -= 1
        draw_state(current_index[0])


def toggle_auto(event):
    auto_play[0] = not auto_play[0]
    autoplay()


def autoplay():
    if auto_play[0] and current_index[0] < len(states) - 1:
        forward()
        fig.canvas.flush_events()
        fig.canvas.start_event_loop(1.0 / fps)
        autoplay()


def run_interface():
    global fps
    try:
        max_n = int(input("Generate cycles up to which number? (e.g., 50): "))
    except ValueError:
        print("Invalid input. Exiting.")
        return

    try:
        fps = int(input("Animation speed (frames per second, e.g., 2 slow, 10 fast): "))
        if fps < 1:
            fps = 1
    except ValueError:
        fps = 2

    prepare_states(max_n)

    print("\nWhat do you want to do?")
    print("1 - Save animation as GIF")
    print("2 - Save animation as MP4")
    print("3 - Export all frames as EPS")
    print("4 - Export a single frame as EPS")
    print("5 - Manual control with buttons")

    choice = input("Choose option (1/2/3/4/5): ")


    os.makedirs("exported_data", exist_ok=True)

    if choice == '1':
        outfile = os.path.join("exported_data", "cycles_animation.gif")
        writer = PillowWriter(fps=fps)
        ani = animation.FuncAnimation(fig, lambda f: draw_state(f),
                                    frames=len(states), blit=False)
        ani.save(outfile, writer=writer)
        print(f"✅ Saved: {outfile}")

    elif choice == '2':
        outfile = os.path.join("exported_data", "cycles_animation.mp4")
        try:
            writer = FFMpegWriter(fps=fps)
        except Exception as e:
            print("❌ FFMpegWriter not available. Is ffmpeg installed and in PATH?")
            print(e)
            return

        ani = animation.FuncAnimation(fig, lambda f: draw_state(f),
                                    frames=len(states), blit=False)
        ani.save(outfile, writer=writer)
        print(f"✅ Saved: {outfile}")

    elif choice == '3':
        # Save each frame as EPS
        for idx in range(len(states)):
            draw_state(idx)
            outfile = os.path.join(EXPORT_DIR, f"frame_{idx:03d}.eps")
            fig.savefig(outfile, format='eps')
        print(f"✅ Saved EPS frames to folder: {EXPORT_DIR}")

    elif choice == '4':
        try:
            frame = int(input(f"Frame index 0..{len(states)-1}: "))
            if 0 <= frame < len(states):
                draw_state(frame)
                outfile = os.path.join(EXPORT_DIR, f"frame_{frame:03d}.eps")
                fig.savefig(outfile, format='eps')
                print(f"✅ Saved: {outfile}")
            else:
                print("Invalid frame index.")
        except ValueError:
            print("Invalid number.")

    else:
        axprev = plt.axes([0.1, 0.05, 0.15, 0.075])
        axnext = plt.axes([0.3, 0.05, 0.15, 0.075])
        axauto = plt.axes([0.55, 0.05, 0.15, 0.075])

        bprev = Button(axprev, '◀️ Back')
        bprev.on_clicked(backward)

        bnext = Button(axnext, '▶️ Forward')
        bnext.on_clicked(forward)

        bauto = Button(axauto, '⏯️ Auto')
        bauto.on_clicked(toggle_auto)

        draw_state(0)
        plt.show()


if __name__ == "__main__":
    run_interface()
