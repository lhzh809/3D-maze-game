#include "raylib.h"
#include <raymath.h>
#include <vector>
#include <cmath>
#include <cstdlib>
#include <ctime>
#include <cstring>
#include <algorithm>
#include <fstream>
#include <string>

//----------------------------------------------------------------------------------
// Game constants
//----------------------------------------------------------------------------------
constexpr int SCREEN_WIDTH       = 1280;
constexpr int SCREEN_HEIGHT      = 720;

constexpr float PLAYER_WIDTH     = 0.3f;
constexpr float PLAYER_HEIGHT    = 1.6f;
constexpr float PLAYER_EYE_Y     = 1.28f;
constexpr float PLAYER_DEPTH     = 0.6f;

constexpr float ENEMY_SIZE       = 0.5f;
constexpr float ENEMY_SPEED      = 0.04f;

constexpr float COIN_RADIUS      = 0.3f;
constexpr float COIN_BOB_AMP     = 0.25f;
constexpr float COIN_BOB_SPEED   = 2.5f;

constexpr float CELL_SIZE        = 2.0f;
constexpr float WALL_THICKNESS   = 0.2f;
constexpr float WALL_HEIGHT      = 2.0f;

constexpr int   ENEMY_COUNT      = 4;
constexpr int   MAX_LIVES        = 3;
constexpr float INVINCIBILITY_TIME = 1.5f;
constexpr int   COIN_COUNT       = 12;
constexpr long long MAX_MAZE_SIZE = 10000000000;   // 改为 long long

// 视锥剔除容差（大幅提高，确保墙壁稳定）
constexpr float FRUSTUM_EPSILON = 10.0f;

//----------------------------------------------------------------------------------
// Dynamic maze dimensions (改为 long long)
//----------------------------------------------------------------------------------
static long long g_mazeWidth = 10;
static long long g_mazeHeight = 10;
static float g_mazeTotalWidth = 0.0f;
static float g_mazeTotalDepth = 0.0f;
static float g_mazeHalfW = 0.0f;
static float g_mazeHalfD = 0.0f;

//----------------------------------------------------------------------------------
// Structures
//----------------------------------------------------------------------------------
struct Enemy {
	Vector3 position;
	int direction;
	int axis;
};

//----------------------------------------------------------------------------------
// Global game state
//----------------------------------------------------------------------------------
static Camera3D camera = { 0 };
static Vector3 playerPos = { 0.0f, PLAYER_EYE_Y, 0.0f };
static std::vector<Vector3> coins;
static std::vector<Enemy> enemies;
static int score = 0;
static int lives = MAX_LIVES;
static bool gameOver = false;
static bool gameWin = false;
static float invincibleTimer = 0.0f;
static bool cursorLocked = true;

static std::vector<BoundingBox> walls;
static std::vector<std::vector<bool>> visited;
static std::vector<std::vector<bool>> rightWall;
static std::vector<std::vector<bool>> bottomWall;

// 单元格墙壁索引缓存
static std::vector<std::vector<std::vector<int>>> cellWalls;

// 当前帧视锥平面
static float g_frustumPlanes[6][4];

// 可见墙壁列表（仅墙壁需要剔除）
static std::vector<int> s_visibleWalls;

// 缓存当前帧的时间
static float g_currentTime = 0.0f;

//----------------------------------------------------------------------------------
// Helper: random float
//----------------------------------------------------------------------------------
static float RandomFloat(float min, float max) {
	return min + static_cast<float>(GetRandomValue(0, 10000)) / 10000.0f * (max - min);
}

//----------------------------------------------------------------------------------
// Load settings from "setting.txt" (解析为 long long)
//----------------------------------------------------------------------------------
static void LoadSettings() {
	long long w = 10, h = 10;
	std::ifstream file("setting.txt");
	if (file.is_open()) {
		std::string line;
		long long values[2] = {0, 0};
		int idx = 0;
		while (std::getline(file, line) && idx < 2) {
			if (line.empty() || line[0] == '#') continue;
			try {
				long long val = std::stoll(line);
				if (val >= 1 && val <= MAX_MAZE_SIZE) {
					values[idx++] = val;
				}
			} catch (...) {}
		}
		file.close();
		if (idx == 2) {
			w = values[0];
			h = values[1];
		}
	}
	g_mazeWidth = w;
	g_mazeHeight = h;
	g_mazeTotalWidth = static_cast<float>(g_mazeWidth) * CELL_SIZE;
	g_mazeTotalDepth = static_cast<float>(g_mazeHeight) * CELL_SIZE;
	g_mazeHalfW = g_mazeTotalWidth * 0.5f;
	g_mazeHalfD = g_mazeTotalDepth * 0.5f;
}

//----------------------------------------------------------------------------------
// Maze generation (DFS) - 使用 long long 索引
//----------------------------------------------------------------------------------
static void CarveMaze(long long x, long long y) {
	visited[static_cast<size_t>(y)][static_cast<size_t>(x)] = true;
	int dirs[4][2] = { {0,-1}, {1,0}, {0,1}, {-1,0} };
	for (int i = 0; i < 4; ++i) {
		int r = GetRandomValue(i, 3);
		int tx = dirs[i][0], ty = dirs[i][1];
		dirs[i][0] = dirs[r][0]; dirs[i][1] = dirs[r][1];
		dirs[r][0] = tx; dirs[r][1] = ty;
	}
	for (int i = 0; i < 4; ++i) {
		long long nx = x + dirs[i][0];
		long long ny = y + dirs[i][1];
		if (nx >= 0 && nx < g_mazeWidth && ny >= 0 && ny < g_mazeHeight && !visited[static_cast<size_t>(ny)][static_cast<size_t>(nx)]) {
			if (dirs[i][0] == 1) rightWall[static_cast<size_t>(y)][static_cast<size_t>(x)] = false;
			else if (dirs[i][0] == -1) rightWall[static_cast<size_t>(ny)][static_cast<size_t>(nx)] = false;
			else if (dirs[i][1] == 1) bottomWall[static_cast<size_t>(y)][static_cast<size_t>(x)] = false;
			else if (dirs[i][1] == -1) bottomWall[static_cast<size_t>(ny)][static_cast<size_t>(nx)] = false;
			CarveMaze(nx, ny);
		}
	}
}

// 构建墙壁并建立单元格-墙壁映射
static void BuildWallBoundingBoxes() {
	walls.clear();
	float minX = -g_mazeHalfW;
	float minZ = -g_mazeHalfD;
	
	// 重新分配 cellWalls 大小 (使用 long long 转 size_t)
	cellWalls.assign(static_cast<size_t>(g_mazeHeight), std::vector<std::vector<int>>(static_cast<size_t>(g_mazeWidth)));
	
	auto addWall = [&](BoundingBox box, long long cellX, long long cellZ) {
		int idx = static_cast<int>(walls.size());
		walls.push_back(box);
		if (cellX >= 0 && cellX < g_mazeWidth && cellZ >= 0 && cellZ < g_mazeHeight) {
			cellWalls[static_cast<size_t>(cellZ)][static_cast<size_t>(cellX)].push_back(idx);
		}
	};
	
	// 外部围墙
	for (long long z = 0; z < g_mazeHeight; ++z) {
		float cz = minZ + static_cast<float>(z) * CELL_SIZE + CELL_SIZE * 0.5f;
		addWall({{minX - WALL_THICKNESS*0.5f, 0, cz - CELL_SIZE*0.5f},
			{minX + WALL_THICKNESS*0.5f, WALL_HEIGHT, cz + CELL_SIZE*0.5f}}, 0, z);
		addWall({{minX + g_mazeTotalWidth - WALL_THICKNESS*0.5f, 0, cz - CELL_SIZE*0.5f},
			{minX + g_mazeTotalWidth + WALL_THICKNESS*0.5f, WALL_HEIGHT, cz + CELL_SIZE*0.5f}}, g_mazeWidth-1, z);
	}
	for (long long x = 0; x < g_mazeWidth; ++x) {
		float cx = minX + static_cast<float>(x) * CELL_SIZE + CELL_SIZE * 0.5f;
		addWall({{cx - CELL_SIZE*0.5f, 0, minZ - WALL_THICKNESS*0.5f},
			{cx + CELL_SIZE*0.5f, WALL_HEIGHT, minZ + WALL_THICKNESS*0.5f}}, x, 0);
		addWall({{cx - CELL_SIZE*0.5f, 0, minZ + g_mazeTotalDepth - WALL_THICKNESS*0.5f},
			{cx + CELL_SIZE*0.5f, WALL_HEIGHT, minZ + g_mazeTotalDepth + WALL_THICKNESS*0.5f}}, x, g_mazeHeight-1);
	}
	
	// 内部墙
	for (long long y = 0; y < g_mazeHeight; ++y) {
		for (long long x = 0; x < g_mazeWidth - 1; ++x) {
			if (rightWall[static_cast<size_t>(y)][static_cast<size_t>(x)]) {
				float cx = minX + static_cast<float>(x+1) * CELL_SIZE;
				float cz = minZ + static_cast<float>(y) * CELL_SIZE + CELL_SIZE * 0.5f;
				BoundingBox box = {{cx - WALL_THICKNESS*0.5f, 0, cz - CELL_SIZE*0.5f},
					{cx + WALL_THICKNESS*0.5f, WALL_HEIGHT, cz + CELL_SIZE*0.5f}};
				addWall(box, x, y);
				addWall(box, x+1, y);
			}
		}
	}
	for (long long y = 0; y < g_mazeHeight - 1; ++y) {
		for (long long x = 0; x < g_mazeWidth; ++x) {
			if (bottomWall[static_cast<size_t>(y)][static_cast<size_t>(x)]) {
				float cx = minX + static_cast<float>(x) * CELL_SIZE + CELL_SIZE * 0.5f;
				float cz = minZ + static_cast<float>(y+1) * CELL_SIZE;
				BoundingBox box = {{cx - CELL_SIZE*0.5f, 0, cz - WALL_THICKNESS*0.5f},
					{cx + CELL_SIZE*0.5f, WALL_HEIGHT, cz + WALL_THICKNESS*0.5f}};
				addWall(box, x, y);
				addWall(box, x, y+1);
			}
		}
	}
}

//----------------------------------------------------------------------------------
// Optimized collision detection (local cell check) - 使用 long long 索引
//----------------------------------------------------------------------------------
static bool CollidesWithWalls(BoundingBox box) {
	Vector3 center = { (box.min.x + box.max.x) * 0.5f, 0, (box.min.z + box.max.z) * 0.5f };
	long long cellX = static_cast<long long>((center.x + g_mazeHalfW) / CELL_SIZE);
	long long cellZ = static_cast<long long>((center.z + g_mazeHalfD) / CELL_SIZE);
	cellX = std::max(0LL, std::min(g_mazeWidth - 1, cellX));
	cellZ = std::max(0LL, std::min(g_mazeHeight - 1, cellZ));
	
	for (long long dz = -1; dz <= 1; ++dz) {
		for (long long dx = -1; dx <= 1; ++dx) {
			long long nx = cellX + dx, nz = cellZ + dz;
			if (nx < 0 || nx >= g_mazeWidth || nz < 0 || nz >= g_mazeHeight) continue;
			for (int idx : cellWalls[static_cast<size_t>(nz)][static_cast<size_t>(nx)]) {
				if (CheckCollisionBoxes(box, walls[idx])) return true;
			}
		}
	}
	return false;
}

// 生成金币时使用全遍历
static bool SphereCollidesWithWalls(Vector3 center, float radius) {
	for (const auto& w : walls) if (CheckCollisionBoxSphere(w, center, radius)) return true;
	return false;
}

//----------------------------------------------------------------------------------
// Generate coin position - 使用 long long 随机
//----------------------------------------------------------------------------------
static Vector3 GenerateCoinPosition() {
	float minX = -g_mazeHalfW, minZ = -g_mazeHalfD;
	Vector3 coin;
	bool valid = false;
	int attempts = 0;
	while (!valid && attempts < 500) {
		long long cx = GetRandomValue(0, static_cast<int>(g_mazeWidth - 1));
		long long cy = GetRandomValue(0, static_cast<int>(g_mazeHeight - 1));
		float cellCX = minX + static_cast<float>(cx) * CELL_SIZE + CELL_SIZE * 0.5f;
		float cellCZ = minZ + static_cast<float>(cy) * CELL_SIZE + CELL_SIZE * 0.5f;
		coin = { cellCX + RandomFloat(-CELL_SIZE*0.35f, CELL_SIZE*0.35f),
			COIN_RADIUS,
			cellCZ + RandomFloat(-CELL_SIZE*0.35f, CELL_SIZE*0.35f) };
		if (!SphereCollidesWithWalls(coin, COIN_RADIUS + 0.1f)) {
			bool tooClose = false;
			for (const auto& c : coins)
				if (Vector3Distance(coin, c) < 1.5f) { tooClose = true; break; }
			if (!tooClose && Vector3Distance(coin, {playerPos.x, 0, playerPos.z}) > 3.0f)
				valid = true;
		}
		attempts++;
	}
	if (!valid) coin = { minX + CELL_SIZE*0.5f, COIN_RADIUS, minZ + CELL_SIZE*0.5f };
	return coin;
}

//----------------------------------------------------------------------------------
// Player movement with collision
//----------------------------------------------------------------------------------
static void MovePlayerWithCollision(Vector3 newPos) {
	Vector3 oldPos = playerPos;
	
	playerPos.x = newPos.x;
	Vector3 body = { playerPos.x, PLAYER_HEIGHT*0.5f, playerPos.z };
	BoundingBox boxX = {
		{ body.x - PLAYER_WIDTH*0.5f, body.y - PLAYER_HEIGHT*0.5f, body.z - PLAYER_DEPTH*0.5f },
		{ body.x + PLAYER_WIDTH*0.5f, body.y + PLAYER_HEIGHT*0.5f, body.z + PLAYER_DEPTH*0.5f }
	};
	if (CollidesWithWalls(boxX)) playerPos.x = oldPos.x;
	
	playerPos.z = newPos.z;
	body = { playerPos.x, PLAYER_HEIGHT*0.5f, playerPos.z };
	BoundingBox boxZ = {
		{ body.x - PLAYER_WIDTH*0.5f, body.y - PLAYER_HEIGHT*0.5f, body.z - PLAYER_DEPTH*0.5f },
		{ body.x + PLAYER_WIDTH*0.5f, body.y + PLAYER_HEIGHT*0.5f, body.z + PLAYER_DEPTH*0.5f }
	};
	if (CollidesWithWalls(boxZ)) playerPos.z = oldPos.z;
	
	playerPos.y = PLAYER_EYE_Y;
}

//----------------------------------------------------------------------------------
// Frustum culling with large tolerance (only for walls)
//----------------------------------------------------------------------------------
static void UpdateFrustumPlanes() {
	Matrix view = GetCameraMatrix(camera);
	float aspect = (float)SCREEN_WIDTH / SCREEN_HEIGHT;
	float fovyRad = camera.fovy * DEG2RAD;
	float top = 0.01f * tanf(fovyRad * 0.5f);
	float bottom = -top;
	float right = top * aspect;
	float left = -right;
	float near = 0.01f;
	float far = 1000.0f;
	
	Matrix proj = {
		2.0f * near / (right - left), 0.0f, 0.0f, 0.0f,
		0.0f, 2.0f * near / (top - bottom), 0.0f, 0.0f,
		(right + left) / (right - left), (top + bottom) / (top - bottom), -(far + near) / (far - near), -1.0f,
		0.0f, 0.0f, -2.0f * far * near / (far - near), 0.0f
	};
	
	Matrix viewProj = MatrixMultiply(view, proj);
	
	float planes[6][4] = {
		{ viewProj.m3 + viewProj.m0, viewProj.m7 + viewProj.m4, viewProj.m11 + viewProj.m8, viewProj.m15 + viewProj.m12 },
		{ viewProj.m3 - viewProj.m0, viewProj.m7 - viewProj.m4, viewProj.m11 - viewProj.m8, viewProj.m15 - viewProj.m12 },
		{ viewProj.m3 + viewProj.m1, viewProj.m7 + viewProj.m5, viewProj.m11 + viewProj.m9, viewProj.m15 + viewProj.m13 },
		{ viewProj.m3 - viewProj.m1, viewProj.m7 - viewProj.m5, viewProj.m11 - viewProj.m9, viewProj.m15 - viewProj.m13 },
		{ viewProj.m3 + viewProj.m2, viewProj.m7 + viewProj.m6, viewProj.m11 + viewProj.m10, viewProj.m15 + viewProj.m14 },
		{ viewProj.m3 - viewProj.m2, viewProj.m7 - viewProj.m6, viewProj.m11 - viewProj.m10, viewProj.m15 - viewProj.m14 }
	};
	for (int i = 0; i < 6; ++i) {
		float len = sqrtf(planes[i][0]*planes[i][0] + planes[i][1]*planes[i][1] + planes[i][2]*planes[i][2]);
		if (len > 0.0001f) {
			g_frustumPlanes[i][0] = planes[i][0] / len;
			g_frustumPlanes[i][1] = planes[i][1] / len;
			g_frustumPlanes[i][2] = planes[i][2] / len;
			g_frustumPlanes[i][3] = planes[i][3] / len;
		}
	}
}

// 仅用于墙壁的宽松检测
static bool IsWallInView(BoundingBox box) {
	float epsilon = FRUSTUM_EPSILON;
	BoundingBox expandedBox = {
		{ box.min.x - epsilon, box.min.y - epsilon, box.min.z - epsilon },
		{ box.max.x + epsilon, box.max.y + epsilon, box.max.z + epsilon }
	};
	
	Vector3 center = { (expandedBox.min.x + expandedBox.max.x) * 0.5f,
		(expandedBox.min.y + expandedBox.max.y) * 0.5f,
		(expandedBox.min.z + expandedBox.max.z) * 0.5f };
	Vector3 half = { (expandedBox.max.x - expandedBox.min.x) * 0.5f,
		(expandedBox.max.y - expandedBox.min.y) * 0.5f,
		(expandedBox.max.z - expandedBox.min.z) * 0.5f };
	
	for (int i = 0; i < 6; ++i) {
		float r = half.x * fabs(g_frustumPlanes[i][0]) +
		half.y * fabs(g_frustumPlanes[i][1]) +
		half.z * fabs(g_frustumPlanes[i][2]);
		float dist = g_frustumPlanes[i][0]*center.x + g_frustumPlanes[i][1]*center.y + g_frustumPlanes[i][2]*center.z + g_frustumPlanes[i][3];
		if (dist + r < -FRUSTUM_EPSILON) return false;
	}
	return true;
}

//----------------------------------------------------------------------------------
// Initialize game - 所有动态分配使用 long long 转 size_t
//----------------------------------------------------------------------------------
void debug(){
	SetWindowPosition(0,760);
	SetWindowOpacity(10);
}
static void InitGame() {
	SetRandomSeed(static_cast<unsigned int>(time(nullptr)));
	LoadSettings();
	
	// 分配迷宫数组
	visited.assign(static_cast<size_t>(g_mazeHeight), std::vector<bool>(static_cast<size_t>(g_mazeWidth), false));
	rightWall.assign(static_cast<size_t>(g_mazeHeight), std::vector<bool>(static_cast<size_t>(g_mazeWidth - 1), true));
	bottomWall.assign(static_cast<size_t>(g_mazeHeight - 1), std::vector<bool>(static_cast<size_t>(g_mazeWidth), true));
	
	CarveMaze(0, 0);
	BuildWallBoundingBoxes();
	
	float startX = -g_mazeHalfW + CELL_SIZE * 0.5f;
	float startZ = -g_mazeHalfD + CELL_SIZE * 0.5f;
	
	camera.position = { startX, PLAYER_EYE_Y, startZ };
	camera.target = { startX, PLAYER_EYE_Y, startZ + 1.0f };
	camera.up = { 0, 1, 0 };
	camera.fovy = 80.0f;
	camera.projection = CAMERA_PERSPECTIVE;
	playerPos = camera.position;
	
	score = 0;
	lives = MAX_LIVES;
	gameOver = false;
	gameWin = false;
	invincibleTimer = 0.0f;
	cursorLocked = true;
	DisableCursor();
	SetMousePosition(GetWindowPosition().x,GetWindowPosition().y);
	coins.clear();
	for (int i = 0; i < COIN_COUNT; ++i) coins.push_back(GenerateCoinPosition());
	
	enemies.clear();
	for (int i = 0; i < ENEMY_COUNT; ++i) {
		Enemy e;
		bool valid = false;
		int attempts = 0;
		while (!valid && attempts < 200) {
			long long cx = GetRandomValue(1, static_cast<int>(g_mazeWidth - 2));
			long long cy = GetRandomValue(1, static_cast<int>(g_mazeHeight - 2));
			float ex = -g_mazeHalfW + static_cast<float>(cx) * CELL_SIZE + CELL_SIZE * 0.5f;
			float ez = -g_mazeHalfD + static_cast<float>(cy) * CELL_SIZE + CELL_SIZE * 0.5f;
			if (Vector3Distance({ex, 0, ez}, {startX, 0, startZ}) > 5.0f) {
				e.position = { ex, ENEMY_SIZE*0.5f, ez };
				e.direction = (GetRandomValue(0,1) == 0) ? -1 : 1;
				e.axis = (GetRandomValue(0,1) == 0) ? 0 : 2;
				valid = true;
			}
			attempts++;
		}
		if (!valid) {
			e.position = { -g_mazeHalfW + CELL_SIZE*2, ENEMY_SIZE*0.5f, -g_mazeHalfD + CELL_SIZE*2 };
			e.direction = 1;
			e.axis = 0;
		}
		enemies.push_back(e);
	}
	
	s_visibleWalls.reserve(static_cast<size_t>(walls.size()));
}

//----------------------------------------------------------------------------------
// Update game
//----------------------------------------------------------------------------------
static void UpdateGame() {
	if (gameOver || gameWin) {
		if (IsKeyPressed(KEY_R)) InitGame();
		return;
	}
	if (IsKeyPressed(KEY_SPACE)) {
		cursorLocked = !cursorLocked;
		if (cursorLocked){ DisableCursor();SetMousePosition(GetWindowPosition().x,GetWindowPosition().y);} else EnableCursor();
	} else if (IsMouseButtonPressed(MOUSE_BUTTON_LEFT)) {
		cursorLocked = true;
		SetMousePosition(GetWindowPosition().x,GetWindowPosition().y);
		DisableCursor();
	}
	
	if (invincibleTimer > 0.0f) invincibleTimer -= GetFrameTime();
	
	if (cursorLocked) {
		UpdateCamera(&camera, CAMERA_FIRST_PERSON);
	}
	Vector3 forward = Vector3Normalize(Vector3Subtract(camera.target, camera.position));
	
	Vector3 newPos = camera.position;
	newPos.x = std::max(-g_mazeHalfW + 0.5f, std::min(g_mazeHalfW - 0.5f, newPos.x));
	newPos.z = std::max(-g_mazeHalfD + 0.5f, std::min(g_mazeHalfD - 0.5f, newPos.z));
	newPos.y = PLAYER_EYE_Y;
	
	MovePlayerWithCollision(newPos);
	
	camera.position = playerPos;
	camera.target = Vector3Add(playerPos, forward);
	
	// 敌人移动
	for (auto& enemy : enemies) {
		Vector3 oldEnemyPos = enemy.position;
		if (enemy.axis == 0) enemy.position.x += enemy.direction * ENEMY_SPEED;
		else                 enemy.position.z += enemy.direction * ENEMY_SPEED;
		BoundingBox enemyBox = {
			{ enemy.position.x - ENEMY_SIZE*0.5f, enemy.position.y - ENEMY_SIZE*0.5f, enemy.position.z - ENEMY_SIZE*0.5f },
			{ enemy.position.x + ENEMY_SIZE*0.5f, enemy.position.y + ENEMY_SIZE*0.5f, enemy.position.z + ENEMY_SIZE*0.5f }
		};
		if (CollidesWithWalls(enemyBox)) {
			enemy.position = oldEnemyPos;
			enemy.direction *= -1;
		}
	}
	
	Vector3 body = { playerPos.x, PLAYER_HEIGHT*0.5f, playerPos.z };
	BoundingBox playerBox = {
		{ body.x - PLAYER_WIDTH*0.5f, body.y - PLAYER_HEIGHT*0.5f, body.z - PLAYER_DEPTH*0.5f },
		{ body.x + PLAYER_WIDTH*0.5f, body.y + PLAYER_HEIGHT*0.5f, body.z + PLAYER_DEPTH*0.5f }
	};
	
	if (invincibleTimer <= 0.0f) {
		for (const auto& enemy : enemies) {
			BoundingBox enemyBox = {
				{ enemy.position.x - ENEMY_SIZE*0.5f, enemy.position.y - ENEMY_SIZE*0.5f, enemy.position.z - ENEMY_SIZE*0.5f },
				{ enemy.position.x + ENEMY_SIZE*0.5f, enemy.position.y + ENEMY_SIZE*0.5f, enemy.position.z + ENEMY_SIZE*0.5f }
			};
			if (CheckCollisionBoxes(playerBox, enemyBox)) {
				lives--;
				if (lives <= 0) { gameOver = true; return; }
				playerPos = { -g_mazeHalfW + CELL_SIZE*0.5f, PLAYER_EYE_Y, -g_mazeHalfD + CELL_SIZE*0.5f };
				camera.position = playerPos;
				forward = Vector3Normalize(Vector3Subtract(camera.target, camera.position));
				camera.target = Vector3Add(playerPos, forward);
				invincibleTimer = INVINCIBILITY_TIME;
				break;
			}
		}
	}
	
	for (auto it = coins.begin(); it != coins.end();) {
		if (CheckCollisionBoxSphere(playerBox, *it, COIN_RADIUS)) {
			score++;
			it = coins.erase(it);
		} else ++it;
	}
	if (coins.empty()) gameWin = true;
	
	g_currentTime = static_cast<float>(GetTime());
}

//----------------------------------------------------------------------------------
// Draw 3D scene (only walls are culled, enemies and coins always drawn)
//----------------------------------------------------------------------------------
static void Draw3DScene() {
	UpdateFrustumPlanes();
	
	// ---- 剔除墙壁 ----
	s_visibleWalls.clear();
	for (size_t i = 0; i < walls.size(); ++i) {
		if (IsWallInView(walls[i])) {
			s_visibleWalls.push_back(static_cast<int>(i));
		}
	}
	
	// ---- 地面（始终绘制） ----
	DrawCube({0, -0.5f, 0}, g_mazeTotalWidth + 1, 1, g_mazeTotalDepth + 1, DARKGRAY);
	DrawCubeWires({0, -0.5f, 0}, g_mazeTotalWidth + 1, 1, g_mazeTotalDepth + 1, GRAY);
	
	// ---- 绘制可见墙壁 ----
	for (int idx : s_visibleWalls) {
		const BoundingBox& w = walls[static_cast<size_t>(idx)];
		Vector3 size = { w.max.x - w.min.x, w.max.y - w.min.y, w.max.z - w.min.z };
		Vector3 center = { (w.min.x + w.max.x)*0.5f, (w.min.y + w.max.y)*0.5f, (w.min.z + w.max.z)*0.5f };
		DrawCube(center, size.x, size.y, size.z, {80, 60, 40, 255});
		DrawCubeWires(center, size.x, size.y, size.z, BLACK);
	}
	
	// ---- 绘制所有敌人（不剔除） ----
	for (const auto& e : enemies) {
		DrawCube(e.position, ENEMY_SIZE, ENEMY_SIZE, ENEMY_SIZE, RED);
		DrawCubeWires(e.position, ENEMY_SIZE, ENEMY_SIZE, ENEMY_SIZE, MAROON);
	}
	
	// ---- 绘制所有金币（不剔除，带浮动动画） ----
	float t = g_currentTime;
	for (const auto& base : coins) {
		Vector3 p = base;
		p.y += sinf(t * COIN_BOB_SPEED) * COIN_BOB_AMP;
		DrawSphere(p, COIN_RADIUS, GOLD);
		DrawSphereWires(p, COIN_RADIUS, 8, 8, ORANGE);
	}
}

//----------------------------------------------------------------------------------
// UI
//----------------------------------------------------------------------------------
static void DrawUI() {
	DrawText(TextFormat("Score: %d", score), 20, 20, 30, GRAY);
	DrawText(TextFormat("Lives: %d", lives), 20, 60, 30, GRAY);
	if (gameWin) DrawText("YOU WIN! Press R to restart.", (SCREEN_WIDTH - MeasureText("YOU WIN! Press R to restart.", 40))/2, SCREEN_HEIGHT/2-20, 40, GREEN);
	if (gameOver) DrawText("GAME OVER! Press R to restart.", (SCREEN_WIDTH - MeasureText("GAME OVER! Press R to restart.", 40))/2, SCREEN_HEIGHT/2-20, 40, RED);
	DrawText("WASD: move | Mouse: look | ESC: toggle cursor | R: restart", 20, SCREEN_HEIGHT-30, 20, LIGHTGRAY);
}

//----------------------------------------------------------------------------------
// Main
//----------------------------------------------------------------------------------
int main() {
	SetConfigFlags(FLAG_VSYNC_HINT);
	SetConfigFlags(FLAG_MSAA_4X_HINT);
	
	InitWindow(SCREEN_WIDTH, SCREEN_HEIGHT, "Maze Collector");
	SetTargetFPS(60);
	InitGame();
	
	while (!WindowShouldClose()) {
		debug();
		UpdateGame();
		BeginDrawing();
		BeginMode3D(camera);
		Draw3DScene();
		EndMode3D();
		DrawUI();
		DrawText(TextFormat("FPS: %d",GetFPS()),
				 SCREEN_WIDTH-250/*SCREEN_WIDTH-100*/,0,
				 50,GRAY);
		/*DrawText(TextFormat("Maze Height: %d",g_mazeHeight),SCREEN_WIDTH-500,0,25,GRAY);
		DrawText(TextFormat("Maze Width: %d",g_mazeWidth),SCREEN_WIDTH-750,0,25,GRAY);*/
		EndDrawing();
	}
	EnableCursor();
	CloseWindow();
	return 0;
}
