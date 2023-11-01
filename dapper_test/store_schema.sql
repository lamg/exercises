CREATE TABLE github_com_lamg_migrate_migration(
    id integer PRIMARY KEY AUTOINCREMENT,
    hash TEXT NOT NULL,
    message text NOT NULL,
    date text NOT NULL,
    dbFile text NOT NULL
);

CREATE TABLE github_com_lamg_migrate_step(
    migrationId integer PRIMARY KEY,
    stepIndex integer NOT NULL,
    reason text NOT NULL
);

CREATE TABLE github_com_lamg_migrate_statement(
    id integer PRIMARY KEY AUTOINCREMENT,
    migrationId integer NOT NULL,
    stepIndex integer NOT NULL,
    statementIndex integer NOT NULL,
    sql text NOT NULL
);

CREATE TABLE github_com_lamg_migrate_error(
    statementId integer PRIMARY KEY,
    error text NOT NULL
);

